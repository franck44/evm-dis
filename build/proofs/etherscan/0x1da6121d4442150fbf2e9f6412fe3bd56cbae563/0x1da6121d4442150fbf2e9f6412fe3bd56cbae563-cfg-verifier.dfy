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
      var s6 := Push2(s5, 0x012c);
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
      var s6 := Push4(s5, 0x715018a6);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x00ad);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s9, gas - 1)
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
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0071);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s5, gas - 1)
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
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0237);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa457c2d7);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x023f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0252);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0265);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x62
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0278);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x012c);
      assert s1.Peek(0) == 0x12c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s2, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 29
    * Starting at 0x12c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c as nat
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

  /** Node 12
    * Segment Id for this node is: 65
    * Starting at 0x278
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x278 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01da);
      var s3 := Push2(s2, 0x0286);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0aad);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s7, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 185
    * Starting at 0xaad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x286

    requires s0.stack[3] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x286;
      assert s1.Peek(3) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0abe);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s10, gas - 1)
      else
        ExecuteFromCFGNode_s14(s10, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 186
    * Starting at 0xabb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x286

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x286;
      assert s1.Peek(5) == 0x1da;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 15
    * Segment Id for this node is: 187
    * Starting at 0xabe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x286

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x286;
      assert s1.Peek(4) == 0x1da;
      var s2 := Push2(s1, 0x0ac7);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s5, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0xac7

    requires s0.stack[5] == 0x286

    requires s0.stack[6] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xac7;
      assert s1.Peek(5) == 0x286;
      assert s1.Peek(6) == 0x1da;
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
      assert s11.Peek(4) == 0xac7;
      assert s11.Peek(8) == 0x286;
      assert s11.Peek(9) == 0x1da;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s14, gas - 1)
      else
        ExecuteFromCFGNode_s17(s14, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xac7

    requires s0.stack[6] == 0x286

    requires s0.stack[7] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xac7;
      assert s1.Peek(7) == 0x286;
      assert s1.Peek(8) == 0x1da;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 18
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xac7

    requires s0.stack[6] == 0x286

    requires s0.stack[7] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac7;
      assert s1.Peek(6) == 0x286;
      assert s1.Peek(7) == 0x1da;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s5, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 188
    * Starting at 0xac7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x286

    requires s0.stack[5] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x286;
      assert s1.Peek(5) == 0x1da;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s7, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 66
    * Starting at 0x286
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
      var s2 := Push2(s1, 0x0611);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s3, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 125
    * Starting at 0x611
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x611 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
      var s2 := Push2(s1, 0x0619);
      var s3 := Push2(s2, 0x067f);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s4, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x619

    requires s0.stack[2] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x619;
      assert s1.Peek(2) == 0x1da;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s4, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 126
    * Starting at 0x619
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x619 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push2(s7, 0x062a);
      var s9 := Push2(s8, 0x053b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s10, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x62a

    requires s0.stack[3] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x62a;
      assert s1.Peek(3) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s11, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 127
    * Starting at 0x62a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0650);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s10, gas - 1)
      else
        ExecuteFromCFGNode_s26(s10, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 128
    * Starting at 0x639
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x639 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x1da;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(3) == 0x1da;
      var s12 := Push2(s11, 0x0dea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s13, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 226
    * Starting at 0xdea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x3b7

    requires s0.stack[3] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(3) == 0x1da;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Dup2(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push32(s9, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x3b7;
      assert s11.Peek(5) == 0x1da;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s18, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1da;
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

  /** Node 29
    * Segment Id for this node is: 129
    * Starting at 0x650
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x650 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0676);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s32(s10, gas - 1)
      else
        ExecuteFromCFGNode_s30(s10, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 130
    * Starting at 0x65f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x1da;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(3) == 0x1da;
      var s12 := Push2(s11, 0x0cb4);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s13, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 221
    * Starting at 0xcb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x3b7

    requires s0.stack[3] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(3) == 0x1da;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x26);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(4) == 0x1da;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 6, 0x646472657373);
      var s17 := Push1(s16, 0xd0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(5) == 0x1da;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s26, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 131
    * Starting at 0x676
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x676 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
      var s2 := Push2(s1, 0x0442);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0953);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s5, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 161
    * Starting at 0x953
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x953 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x442

    requires s0.stack[3] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x442;
      assert s1.Peek(3) == 0x1da;
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
      assert s11.Peek(6) == 0x442;
      assert s11.Peek(8) == 0x1da;
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
      assert s21.Peek(7) == 0x442;
      assert s21.Peek(9) == 0x1da;
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
      assert s31.Peek(5) == 0x442;
      assert s31.Peek(7) == 0x1da;
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
      ExecuteFromCFGNode_s34(s40, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 96
    * Starting at 0x442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s3, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 47
    * Starting at 0x1da
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1da as nat
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

  /** Node 36
    * Segment Id for this node is: 63
    * Starting at 0x265
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0177);
      var s3 := Push2(s2, 0x0273);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0ace);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s7, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 189
    * Starting at 0xace
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xace as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x273

    requires s0.stack[3] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x273;
      assert s1.Peek(3) == 0x177;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0ae0);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s11, gas - 1)
      else
        ExecuteFromCFGNode_s38(s11, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 190
    * Starting at 0xadd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x273

    requires s0.stack[5] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0x273;
      assert s1.Peek(6) == 0x177;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 39
    * Segment Id for this node is: 191
    * Starting at 0xae0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x273

    requires s0.stack[5] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x273;
      assert s1.Peek(5) == 0x177;
      var s2 := Push2(s1, 0x0ae9);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s5, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xae9

    requires s0.stack[6] == 0x273

    requires s0.stack[7] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae9;
      assert s1.Peek(6) == 0x273;
      assert s1.Peek(7) == 0x177;
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
      assert s11.Peek(4) == 0xae9;
      assert s11.Peek(9) == 0x273;
      assert s11.Peek(10) == 0x177;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s14, gas - 1)
      else
        ExecuteFromCFGNode_s41(s14, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xae9

    requires s0.stack[7] == 0x273

    requires s0.stack[8] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xae9;
      assert s1.Peek(8) == 0x273;
      assert s1.Peek(9) == 0x177;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 42
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xae9

    requires s0.stack[7] == 0x273

    requires s0.stack[8] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xae9;
      assert s1.Peek(7) == 0x273;
      assert s1.Peek(8) == 0x177;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s5, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 192
    * Starting at 0xae9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x273

    requires s0.stack[6] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x273;
      assert s1.Peek(6) == 0x177;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0af7);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a86);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s9, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xaf7

    requires s0.stack[6] == 0x273

    requires s0.stack[7] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaf7;
      assert s1.Peek(6) == 0x273;
      assert s1.Peek(7) == 0x177;
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
      assert s11.Peek(4) == 0xaf7;
      assert s11.Peek(9) == 0x273;
      assert s11.Peek(10) == 0x177;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s14, gas - 1)
      else
        ExecuteFromCFGNode_s45(s14, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xaf7

    requires s0.stack[7] == 0x273

    requires s0.stack[8] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xaf7;
      assert s1.Peek(8) == 0x273;
      assert s1.Peek(9) == 0x177;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 46
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xaf7

    requires s0.stack[7] == 0x273

    requires s0.stack[8] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaf7;
      assert s1.Peek(7) == 0x273;
      assert s1.Peek(8) == 0x177;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s5, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 193
    * Starting at 0xaf7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x273

    requires s0.stack[6] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x273;
      assert s1.Peek(6) == 0x177;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s9, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 64
    * Starting at 0x273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x177;
      var s2 := Push2(s1, 0x05e6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s3, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 124
    * Starting at 0x5e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x177;
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
      assert s11.Peek(4) == 0x177;
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
      assert s21.Peek(7) == 0x177;
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
      assert s31.Peek(4) == 0x177;
      var s32 := MStore(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s36, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 37
    * Starting at 0x177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0146);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0f5e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s8, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 232
    * Starting at 0xf5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x146;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s8, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 32
    * Starting at 0x146
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146 as nat
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

  /** Node 53
    * Segment Id for this node is: 61
    * Starting at 0x252
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x252 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0162);
      var s3 := Push2(s2, 0x0260);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0b3b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s7, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 199
    * Starting at 0xb3b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x260

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x260;
      assert s1.Peek(3) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0b4d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s11, gas - 1)
      else
        ExecuteFromCFGNode_s55(s11, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 200
    * Starting at 0xb4a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x260

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x260;
      assert s1.Peek(6) == 0x162;
      var s2 := Dup3(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 56
    * Segment Id for this node is: 201
    * Starting at 0xb4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x260

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x260;
      assert s1.Peek(5) == 0x162;
      var s2 := Push2(s1, 0x0b56);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s5, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb56

    requires s0.stack[6] == 0x260

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb56;
      assert s1.Peek(6) == 0x260;
      assert s1.Peek(7) == 0x162;
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
      assert s11.Peek(4) == 0xb56;
      assert s11.Peek(9) == 0x260;
      assert s11.Peek(10) == 0x162;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s14, gas - 1)
      else
        ExecuteFromCFGNode_s58(s14, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb56

    requires s0.stack[7] == 0x260

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xb56;
      assert s1.Peek(8) == 0x260;
      assert s1.Peek(9) == 0x162;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 59
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb56

    requires s0.stack[7] == 0x260

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb56;
      assert s1.Peek(7) == 0x260;
      assert s1.Peek(8) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s5, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 202
    * Starting at 0xb56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x260

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x260;
      assert s1.Peek(6) == 0x162;
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
      assert s11.Peek(1) == 0x260;
      assert s11.Peek(4) == 0x162;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s13, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 62
    * Starting at 0x260
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      var s2 := Push2(s1, 0x05d2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s3, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 122
    * Starting at 0x5d2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0331);
      var s4 := Push2(s3, 0x05df);
      var s5 := Push2(s4, 0x067f);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s6, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x5df

    requires s0.stack[1] == 0x331

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5df;
      assert s1.Peek(1) == 0x331;
      assert s1.Peek(5) == 0x162;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s4, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 123
    * Starting at 0x5df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x331

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x331;
      assert s1.Peek(5) == 0x162;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x0737);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s5, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 140
    * Starting at 0x737
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x737 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(7) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x075d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s10, gas - 1)
      else
        ExecuteFromCFGNode_s66(s10, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 141
    * Starting at 0x746
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x746 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x331;
      assert s11.Peek(9) == 0x162;
      var s12 := Push2(s11, 0x0e90);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s13, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 229
    * Starting at 0xe90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x331

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(9) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x25);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(10) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 5, 0x6472657373);
      var s17 := Push1(s16, 0xd8);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x331;
      assert s21.Peek(11) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s26, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x331

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x162;
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

  /** Node 69
    * Segment Id for this node is: 142
    * Starting at 0x75d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(7) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0783);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s10, gas - 1)
      else
        ExecuteFromCFGNode_s70(s10, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 143
    * Starting at 0x76c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x331;
      assert s11.Peek(9) == 0x162;
      var s12 := Push2(s11, 0x0c2f);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s13, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 219
    * Starting at 0xc2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x331

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(9) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x23);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(10) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push3(s15, 0x657373);
      var s17 := Push1(s16, 0xe8);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x331;
      assert s21.Peek(11) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s26, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 144
    * Starting at 0x783
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(7) == 0x162;
      var s2 := Push2(s1, 0x078e);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09a3);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s7, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 162
    * Starting at 0x9a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0a12);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s10, gas - 1)
      else
        ExecuteFromCFGNode_s74(s10, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 163
    * Starting at 0x9b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09ba);
      assert s1.Peek(0) == 0x9ba;
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Push2(s1, 0x053b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s3, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x9ba

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9ba;
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s11, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 164
    * Starting at 0x9ba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(8) == 0x78e;
      assert s11.Peek(12) == 0x331;
      assert s11.Peek(16) == 0x162;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := Dup1(s15);
      var s17 := Push2(s16, 0x09f1);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s18, gas - 1)
      else
        ExecuteFromCFGNode_s77(s18, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 165
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push2(s1, 0x09dc);
      var s3 := Push2(s2, 0x053b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s4, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x9dc

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9dc;
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s11, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 166
    * Starting at 0x9dc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup3(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(8) == 0x78e;
      assert s11.Peek(12) == 0x331;
      assert s11.Peek(16) == 0x162;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s15, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 167
    * Starting at 0x9f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Push2(s1, 0x0a0d);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s3, gas - 1)
      else
        ExecuteFromCFGNode_s81(s3, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 168
    * Starting at 0x9f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x78e;
      assert s11.Peek(9) == 0x331;
      assert s11.Peek(13) == 0x162;
      var s12 := Push2(s11, 0x0e60);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s13, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 228
    * Starting at 0xe60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x78e

    requires s0.stack[9] == 0x331

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x78e;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(13) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x16);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 22, 0x1d1c98591a5b99c81a5cc81b9bdd081cdd185c9d1959);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x78e;
      assert s11.Peek(10) == 0x331;
      assert s11.Peek(14) == 0x162;
      var s12 := Push1(s11, 0x52);
      var s13 := Shl(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s21, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
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

  /** Node 84
    * Segment Id for this node is: 169
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push2(s1, 0x094e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s3, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 160
    * Starting at 0x94e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s5, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 145
    * Starting at 0x78e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(7) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(10) == 0x162;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup2(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x331;
      assert s21.Peek(10) == 0x162;
      var s22 := Lt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x07c7);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s25, gas - 1)
      else
        ExecuteFromCFGNode_s87(s25, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 146
    * Starting at 0x7b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x331

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(9) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(10) == 0x162;
      var s12 := Push2(s11, 0x0d3c);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s13, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 223
    * Starting at 0xd3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x3b7

    requires s0.stack[6] == 0x331

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(6) == 0x331;
      assert s1.Peek(10) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x26);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(7) == 0x331;
      assert s11.Peek(11) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 6, 0x616c616e6365);
      var s17 := Push1(s16, 0xd0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(8) == 0x331;
      assert s21.Peek(12) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s26, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x331

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(9) == 0x162;
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

  /** Node 90
    * Segment Id for this node is: 147
    * Starting at 0x7c7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x331

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x162;
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
      assert s11.Peek(7) == 0x331;
      assert s11.Peek(11) == 0x162;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Keccak256(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(9) == 0x331;
      assert s21.Peek(13) == 0x162;
      var s22 := Dup6(s21);
      var s23 := Sub(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Swap2(s25);
      var s27 := Dup6(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x331;
      assert s31.Peek(10) == 0x162;
      var s32 := Dup2(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Dup5(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x07fe);
      var s40 := Swap1(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s91(s41, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 148
    * Starting at 0x7f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x7fe

    requires s0.stack[10] == 0x331

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0x7fe;
      assert s1.Peek(10) == 0x331;
      assert s1.Peek(14) == 0x162;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s3, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x7fe

    requires s0.stack[10] == 0x331

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7fe;
      assert s1.Peek(10) == 0x331;
      assert s1.Peek(14) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s9, gas - 1)
      else
        ExecuteFromCFGNode_s93(s9, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x7fe

    requires s0.stack[11] == 0x331

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0x7fe;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(16) == 0x162;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s3, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0x7fe

    requires s0.stack[12] == 0x331

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0x7fe;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(16) == 0x162;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0x7fe;
      assert s11.Peek(14) == 0x331;
      assert s11.Peek(18) == 0x162;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 95
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x7fe

    requires s0.stack[11] == 0x331

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7fe;
      assert s1.Peek(11) == 0x331;
      assert s1.Peek(15) == 0x162;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s5, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 149
    * Starting at 0x7fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0x331;
      assert s11.Peek(11) == 0x162;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0x331;
      assert s21.Peek(11) == 0x162;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x0848);
      var s28 := Swap2(s27);
      var s29 := Swap1(s28);
      var s30 := Push2(s29, 0x0f5e);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s31, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 232
    * Starting at 0xf5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x848

    requires s0.stack[10] == 0x331

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x848;
      assert s1.Peek(10) == 0x331;
      assert s1.Peek(14) == 0x162;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s8, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 150
    * Starting at 0x848
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x848 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x085b);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(2) == 0x85b;
      assert s11.Peek(7) == 0x331;
      assert s11.Peek(11) == 0x162;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x094e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s14, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 160
    * Starting at 0x94e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x85b

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x85b;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s5, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 151
    * Starting at 0x85b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x331

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x162;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s6, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 78
    * Starting at 0x331
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x162;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s8, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 35
    * Starting at 0x162
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0146);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0bd1);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s8, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 212
    * Starting at 0xbd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x146;
      var s2 := Swap1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s10, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 170
    * Starting at 0xa12
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a2b);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s9, gas - 1)
      else
        ExecuteFromCFGNode_s105(s9, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 171
    * Starting at 0xa1f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := And(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s106(s8, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 172
    * Starting at 0xa2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x094e);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s4, gas - 1)
      else
        ExecuteFromCFGNode_s107(s4, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 173
    * Starting at 0xa31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x07);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0a3d);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x04b4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s7, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 102
    * Starting at 0x4b4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xa3d

    requires s0.stack[7] == 0x78e

    requires s0.stack[11] == 0x331

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa3d;
      assert s1.Peek(7) == 0x78e;
      assert s1.Peek(11) == 0x331;
      assert s1.Peek(15) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0xa3d;
      assert s11.Peek(10) == 0x78e;
      assert s11.Peek(14) == 0x331;
      assert s11.Peek(18) == 0x162;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s109(s19, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xa3d

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x331

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa3d;
      assert s1.Peek(8) == 0x78e;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(16) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s5, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 174
    * Starting at 0xa3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x78e

    requires s0.stack[10] == 0x331

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x78e;
      assert s1.Peek(10) == 0x331;
      assert s1.Peek(14) == 0x162;
      var s2 := Push2(s1, 0x0a47);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0f75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s6, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xa47

    requires s0.stack[7] == 0x78e

    requires s0.stack[11] == 0x331

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa47;
      assert s1.Peek(7) == 0x78e;
      assert s1.Peek(11) == 0x331;
      assert s1.Peek(15) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s9, gas - 1)
      else
        ExecuteFromCFGNode_s112(s9, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xa47

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x331

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa47;
      assert s1.Peek(9) == 0x78e;
      assert s1.Peek(13) == 0x331;
      assert s1.Peek(17) == 0x162;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s3, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0xa47

    requires s0.stack[9] == 0x78e

    requires s0.stack[13] == 0x331

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa47;
      assert s1.Peek(9) == 0x78e;
      assert s1.Peek(13) == 0x331;
      assert s1.Peek(17) == 0x162;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0xa47;
      assert s11.Peek(11) == 0x78e;
      assert s11.Peek(15) == 0x331;
      assert s11.Peek(19) == 0x162;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 114
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xa47

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x331

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa47;
      assert s1.Peek(8) == 0x78e;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(16) == 0x162;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s5, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 175
    * Starting at 0xa47
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa47 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x78e

    requires s0.stack[9] == 0x331

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x78e;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(13) == 0x162;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a6a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s7, gas - 1)
      else
        ExecuteFromCFGNode_s116(s7, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 176
    * Starting at 0xa50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push1(s1, 0x08);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x0a5d);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x04b4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s8, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 102
    * Starting at 0x4b4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xa5d

    requires s0.stack[7] == 0x78e

    requires s0.stack[11] == 0x331

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa5d;
      assert s1.Peek(7) == 0x78e;
      assert s1.Peek(11) == 0x331;
      assert s1.Peek(15) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0xa5d;
      assert s11.Peek(10) == 0x78e;
      assert s11.Peek(14) == 0x331;
      assert s11.Peek(18) == 0x162;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s118(s19, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xa5d

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x331

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa5d;
      assert s1.Peek(8) == 0x78e;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(16) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s5, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 177
    * Starting at 0xa5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x78e

    requires s0.stack[10] == 0x331

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x78e;
      assert s1.Peek(10) == 0x331;
      assert s1.Peek(14) == 0x162;
      var s2 := Push2(s1, 0x0a67);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0f75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s6, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xa67

    requires s0.stack[7] == 0x78e

    requires s0.stack[11] == 0x331

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa67;
      assert s1.Peek(7) == 0x78e;
      assert s1.Peek(11) == 0x331;
      assert s1.Peek(15) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s9, gas - 1)
      else
        ExecuteFromCFGNode_s121(s9, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xa67

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x331

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa67;
      assert s1.Peek(9) == 0x78e;
      assert s1.Peek(13) == 0x331;
      assert s1.Peek(17) == 0x162;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s3, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0xa67

    requires s0.stack[9] == 0x78e

    requires s0.stack[13] == 0x331

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa67;
      assert s1.Peek(9) == 0x78e;
      assert s1.Peek(13) == 0x331;
      assert s1.Peek(17) == 0x162;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0xa67;
      assert s11.Peek(11) == 0x78e;
      assert s11.Peek(15) == 0x331;
      assert s11.Peek(19) == 0x162;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 123
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xa67

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x331

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa67;
      assert s1.Peek(8) == 0x78e;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(16) == 0x162;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s5, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 178
    * Starting at 0xa67
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x78e

    requires s0.stack[9] == 0x331

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x78e;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(13) == 0x162;
      var s2 := Lt(s1);
      var s3 := IsZero(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s125(s3, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 179
    * Starting at 0xa6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x331

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := Push2(s1, 0x094e);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s3, gas - 1)
      else
        ExecuteFromCFGNode_s126(s3, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 180
    * Starting at 0xa6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(12) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x78e;
      assert s11.Peek(9) == 0x331;
      assert s11.Peek(13) == 0x162;
      var s12 := Push2(s11, 0x0d82);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s13, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 224
    * Starting at 0xd82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x78e

    requires s0.stack[9] == 0x331

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x78e;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(13) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x06);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 6, 0x119bdc989a59);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x78e;
      assert s11.Peek(10) == 0x331;
      assert s11.Peek(14) == 0x162;
      var s12 := Push1(s11, 0xd2);
      var s13 := Shl(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s21, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 59
    * Starting at 0x23f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0162);
      var s3 := Push2(s2, 0x024d);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0b3b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s7, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 199
    * Starting at 0xb3b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x24d

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24d;
      assert s1.Peek(3) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0b4d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s11, gas - 1)
      else
        ExecuteFromCFGNode_s130(s11, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 200
    * Starting at 0xb4a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x24d

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x24d;
      assert s1.Peek(6) == 0x162;
      var s2 := Dup3(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 131
    * Segment Id for this node is: 201
    * Starting at 0xb4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x24d

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x24d;
      assert s1.Peek(5) == 0x162;
      var s2 := Push2(s1, 0x0b56);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s5, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb56

    requires s0.stack[6] == 0x24d

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb56;
      assert s1.Peek(6) == 0x24d;
      assert s1.Peek(7) == 0x162;
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
      assert s11.Peek(4) == 0xb56;
      assert s11.Peek(9) == 0x24d;
      assert s11.Peek(10) == 0x162;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s14, gas - 1)
      else
        ExecuteFromCFGNode_s133(s14, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb56

    requires s0.stack[7] == 0x24d

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xb56;
      assert s1.Peek(8) == 0x24d;
      assert s1.Peek(9) == 0x162;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 134
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb56

    requires s0.stack[7] == 0x24d

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb56;
      assert s1.Peek(7) == 0x24d;
      assert s1.Peek(8) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s5, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 202
    * Starting at 0xb56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x24d

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x24d;
      assert s1.Peek(6) == 0x162;
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
      assert s11.Peek(1) == 0x24d;
      assert s11.Peek(4) == 0x162;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s13, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 60
    * Starting at 0x24d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      var s2 := Push2(s1, 0x0559);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s3, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 115
    * Starting at 0x559
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x559 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x0568);
      var s7 := Push2(s6, 0x067f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s8, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x568

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x568;
      assert s1.Peek(7) == 0x162;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s4, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 116
    * Starting at 0x568
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x568 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Dup3(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x162;
      var s12 := Push1(s11, 0x20);
      var s13 := Dup1(s12);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Swap2(s20);
      assert s21.Peek(8) == 0x162;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := Push1(s23, 0x00);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := Keccak256(s26);
      var s28 := Swap2(s27);
      var s29 := Dup9(s28);
      var s30 := And(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(10) == 0x162;
      var s32 := MStore(s31);
      var s33 := Swap3(s32);
      var s34 := MStore(s33);
      var s35 := Swap1(s34);
      var s36 := Keccak256(s35);
      var s37 := SLoad(s36);
      var s38 := Swap1(s37);
      var s39 := Pop(s38);
      var s40 := Dup3(s39);
      var s41 := Dup2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s140(s41, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 117
    * Starting at 0x597
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x597 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Lt(s0);
      assert s1.Peek(5) == 0x162;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x05b4);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s4, gas - 1)
      else
        ExecuteFromCFGNode_s141(s4, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 118
    * Starting at 0x59d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(6) == 0x162;
      var s12 := Push2(s11, 0x0f19);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s13, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 231
    * Starting at 0xf19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x3b7

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(6) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x25);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a2064656372656173656420616c6c6f77616e63652062656c6f77);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(7) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 5, 0x207a65726f);
      var s17 := Push1(s16, 0xd8);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(8) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s26, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x162;
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

  /** Node 144
    * Segment Id for this node is: 119
    * Starting at 0x5b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x162;
      var s2 := Push2(s1, 0x05c8);
      var s3 := Push2(s2, 0x05bf);
      var s4 := Push2(s3, 0x067f);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s5, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x5bf

    requires s0.stack[1] == 0x5c8

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5bf;
      assert s1.Peek(1) == 0x5c8;
      assert s1.Peek(6) == 0x162;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s4, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 120
    * Starting at 0x5bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x5c8

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5c8;
      assert s1.Peek(6) == 0x162;
      var s2 := Dup6(s1);
      var s3 := Dup6(s2);
      var s4 := Dup5(s3);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0683);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s7, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 133
    * Starting at 0x683
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5c8

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5c8;
      assert s1.Peek(8) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06a9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s10, gas - 1)
      else
        ExecuteFromCFGNode_s148(s10, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 134
    * Starting at 0x692
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x692 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5c8

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5c8;
      assert s1.Peek(9) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x5c8;
      assert s11.Peek(10) == 0x162;
      var s12 := Push2(s11, 0x0ed5);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s13, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 230
    * Starting at 0xed5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x5c8

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x5c8;
      assert s1.Peek(10) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x24);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x5c8;
      assert s11.Peek(11) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push4(s15, 0x72657373);
      var s17 := Push1(s16, 0xe0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x5c8;
      assert s21.Peek(12) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s26, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5c8

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5c8;
      assert s1.Peek(9) == 0x162;
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
    * Segment Id for this node is: 135
    * Starting at 0x6a9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5c8

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5c8;
      assert s1.Peek(8) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06cf);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s10, gas - 1)
      else
        ExecuteFromCFGNode_s152(s10, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 136
    * Starting at 0x6b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5c8

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5c8;
      assert s1.Peek(9) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x5c8;
      assert s11.Peek(10) == 0x162;
      var s12 := Push2(s11, 0x0cfa);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s13, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 222
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x5c8

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x5c8;
      assert s1.Peek(10) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x5c8;
      assert s11.Peek(11) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x7373);
      var s17 := Push1(s16, 0xf0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x5c8;
      assert s21.Peek(12) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s26, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 137
    * Starting at 0x6cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5c8

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5c8;
      assert s1.Peek(8) == 0x162;
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
      assert s11.Peek(7) == 0x5c8;
      assert s11.Peek(12) == 0x162;
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
      assert s21.Peek(10) == 0x5c8;
      assert s21.Peek(15) == 0x162;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Dup8(s23);
      var s25 := And(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := MStore(s27);
      var s29 := Swap5(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(9) == 0x5c8;
      assert s31.Peek(14) == 0x162;
      var s32 := MStore(s31);
      var s33 := Swap1(s32);
      var s34 := Dup2(s33);
      var s35 := Swap1(s34);
      var s36 := Keccak256(s35);
      var s37 := Dup5(s36);
      var s38 := Swap1(s37);
      var s39 := SStore(s38);
      var s40 := MLoad(s39);
      var s41 := Push32(s40, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s155(s41, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 138
    * Starting at 0x71f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x5c8

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(7) == 0x5c8;
      assert s1.Peek(12) == 0x162;
      var s2 := Push2(s1, 0x072a);
      var s3 := Swap1(s2);
      var s4 := Dup6(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0f5e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s7, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 232
    * Starting at 0xf5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x72a

    requires s0.stack[9] == 0x5c8

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x72a;
      assert s1.Peek(9) == 0x5c8;
      assert s1.Peek(14) == 0x162;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s8, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 139
    * Starting at 0x72a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x5c8

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5c8;
      assert s1.Peek(12) == 0x162;
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
      assert s11.Peek(0) == 0x5c8;
      assert s11.Peek(5) == 0x162;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s12, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 121
    * Starting at 0x5c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x162;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s9, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 58
    * Starting at 0x237
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x237 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0139);
      var s3 := Push2(s2, 0x054a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s4, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 114
    * Starting at 0x54a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x05);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x029a);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0fa4);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s9, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 240
    * Starting at 0xfa4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x29a

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x29a;
      assert s1.Peek(4) == 0x139;
      var s2 := Push1(s1, 0x02);
      var s3 := Dup2(s2);
      var s4 := Div(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Dup3(s5);
      var s7 := And(s6);
      var s8 := Dup1(s7);
      var s9 := Push2(s8, 0x0fb8);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s163(s10, gas - 1)
      else
        ExecuteFromCFGNode_s162(s10, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 241
    * Starting at 0xfb2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x29a

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x29a;
      assert s1.Peek(7) == 0x139;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s163(s5, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 242
    * Starting at 0xfb8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x29a

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x29a;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0fd9);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s9, gas - 1)
      else
        ExecuteFromCFGNode_s164(s9, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 243
    * Starting at 0xfc4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x29a

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x29a;
      assert s1.Peek(7) == 0x139;
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

  /** Node 165
    * Segment Id for this node is: 244
    * Starting at 0xfd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x29a

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x29a;
      assert s1.Peek(6) == 0x139;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s6, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 68
    * Starting at 0x29a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x139;
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
      assert s11.Peek(4) == 0x139;
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
      assert s21.Peek(5) == 0x139;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x02c6);
      assert s31.Peek(0) == 0x2c6;
      assert s31.Peek(8) == 0x139;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0fa4);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s34, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 240
    * Starting at 0xfa4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x2c6

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2c6;
      assert s1.Peek(8) == 0x139;
      var s2 := Push1(s1, 0x02);
      var s3 := Dup2(s2);
      var s4 := Div(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Dup3(s5);
      var s7 := And(s6);
      var s8 := Dup1(s7);
      var s9 := Push2(s8, 0x0fb8);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s10, gas - 1)
      else
        ExecuteFromCFGNode_s168(s10, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 241
    * Starting at 0xfb2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2c6

    requires s0.stack[10] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x2c6;
      assert s1.Peek(11) == 0x139;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s169(s5, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 242
    * Starting at 0xfb8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2c6

    requires s0.stack[10] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2c6;
      assert s1.Peek(10) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0fd9);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s171(s9, gas - 1)
      else
        ExecuteFromCFGNode_s170(s9, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 243
    * Starting at 0xfc4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2c6

    requires s0.stack[10] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x2c6;
      assert s1.Peek(11) == 0x139;
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

  /** Node 171
    * Segment Id for this node is: 244
    * Starting at 0xfd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2c6

    requires s0.stack[10] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2c6;
      assert s1.Peek(10) == 0x139;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s6, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 69
    * Starting at 0x2c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x139;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0313);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s5, gas - 1)
      else
        ExecuteFromCFGNode_s173(s5, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 70
    * Starting at 0x2cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x139;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x02e8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s5, gas - 1)
      else
        ExecuteFromCFGNode_s174(s5, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 71
    * Starting at 0x2d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x139;
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
      assert s11.Peek(7) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0313);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s14, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 75
    * Starting at 0x313
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x313 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x139;
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
      ExecuteFromCFGNode_s176(s10, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 31
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0146);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0bdc);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s8, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 213
    * Starting at 0xbdc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x146;
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
      assert s11.Peek(8) == 0x146;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Dup3(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s178(s14, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 214
    * Starting at 0xbec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x146;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c08);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s180(s7, gas - 1)
      else
        ExecuteFromCFGNode_s179(s7, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 215
    * Starting at 0xbf5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x146;
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
      assert s11.Peek(8) == 0x146;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0bec);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s16, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 216
    * Starting at 0xc08
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x146;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c19);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s7, gas - 1)
      else
        ExecuteFromCFGNode_s181(s7, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 217
    * Starting at 0xc11
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x146;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s182(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 218
    * Starting at 0xc19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x146;
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
      assert s11.Peek(4) == 0x146;
      var s12 := Push1(s11, 0x40);
      var s13 := Add(s12);
      var s14 := Swap4(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s19, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 72
    * Starting at 0x2e8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x139;
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
      ExecuteFromCFGNode_s184(s11, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 73
    * Starting at 0x2f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x139;
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
      assert s11.Peek(7) == 0x139;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x02f6);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s16, gas - 1)
      else
        ExecuteFromCFGNode_s185(s16, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 74
    * Starting at 0x30a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x139;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s175(s8, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 11
    * Starting at 0x71
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71 as nat
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
      var s5 := Push2(s4, 0x0202);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s208(s6, gas - 1)
      else
        ExecuteFromCFGNode_s187(s6, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8091f3bf);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x020a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s5, gas - 1)
      else
        ExecuteFromCFGNode_s188(s5, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x860a32ec);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0212);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s5, gas - 1)
      else
        ExecuteFromCFGNode_s189(s5, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 14
    * Starting at 0x93
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x89f9a1d3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x021a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s5, gas - 1)
      else
        ExecuteFromCFGNode_s190(s5, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 15
    * Starting at 0x9e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0222);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s5, gas - 1)
      else
        ExecuteFromCFGNode_s191(s5, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 16
    * Starting at 0xa9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x012c);
      assert s1.Peek(0) == 0x12c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s2, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 56
    * Starting at 0x222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x022a);
      var s3 := Push2(s2, 0x053b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s4, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x22a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x22a;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s11, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 57
    * Starting at 0x22a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0146);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0bbd);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s8, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 211
    * Starting at 0xbbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x146;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x146;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s16, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 55
    * Starting at 0x21a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0177);
      var s3 := Push2(s2, 0x0535);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s4, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 112
    * Starting at 0x535
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x535 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x177;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s5, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 37
    * Starting at 0x177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x177;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0146);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0f5e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s8, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 232
    * Starting at 0xf5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x146

    requires s0.stack[3] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x146;
      assert s1.Peek(3) == 0x177;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s8, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 32
    * Starting at 0x146
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x177;
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

  /** Node 201
    * Segment Id for this node is: 54
    * Starting at 0x212
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x212 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0162);
      var s3 := Push2(s2, 0x052c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s4, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 111
    * Starting at 0x52c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x162;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Dup2(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s7, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 35
    * Starting at 0x162
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x162;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0146);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0bd1);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s8, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 212
    * Starting at 0xbd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x146

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x146;
      assert s1.Peek(3) == 0x162;
      var s2 := Swap1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s10, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 32
    * Starting at 0x146
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x162;
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

  /** Node 206
    * Segment Id for this node is: 53
    * Starting at 0x20a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0162);
      var s3 := Push2(s2, 0x051e);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s4, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 110
    * Starting at 0x51e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x162;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s10, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 52
    * Starting at 0x202
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x202 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01da);
      var s3 := Push2(s2, 0x04d3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s4, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 104
    * Starting at 0x4d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1da;
      var s2 := Push2(s1, 0x04db);
      var s3 := Push2(s2, 0x067f);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s4, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4db

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4db;
      assert s1.Peek(1) == 0x1da;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s4, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 105
    * Starting at 0x4db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push2(s7, 0x04ec);
      var s9 := Push2(s8, 0x053b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s10, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x4ec

    requires s0.stack[2] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4ec;
      assert s1.Peek(2) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s11, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 106
    * Starting at 0x4ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0512);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s217(s10, gas - 1)
      else
        ExecuteFromCFGNode_s214(s10, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 107
    * Starting at 0x4fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x1da;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(2) == 0x1da;
      var s12 := Push2(s11, 0x0dea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s13, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 226
    * Starting at 0xdea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x3b7

    requires s0.stack[2] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(2) == 0x1da;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Dup2(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push32(s9, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x3b7;
      assert s11.Peek(4) == 0x1da;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s18, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
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

  /** Node 217
    * Segment Id for this node is: 108
    * Starting at 0x512
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x512 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1da;
      var s2 := Push2(s1, 0x051c);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0953);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s5, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 161
    * Starting at 0x953
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x953 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x51c

    requires s0.stack[2] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x51c;
      assert s1.Peek(2) == 0x1da;
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
      assert s11.Peek(6) == 0x51c;
      assert s11.Peek(7) == 0x1da;
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
      assert s21.Peek(7) == 0x51c;
      assert s21.Peek(8) == 0x1da;
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
      assert s31.Peek(5) == 0x51c;
      assert s31.Peek(6) == 0x1da;
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
      ExecuteFromCFGNode_s219(s40, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 109
    * Starting at 0x51c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1da;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s2, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 17
    * Starting at 0xad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x313ce567);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00f4);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s356(s6, gas - 1)
      else
        ExecuteFromCFGNode_s221(s6, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 18
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x019f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s352(s5, gas - 1)
      else
        ExecuteFromCFGNode_s222(s5, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 19
    * Starting at 0xc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x39509351);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01b4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s322(s5, gas - 1)
      else
        ExecuteFromCFGNode_s223(s5, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 20
    * Starting at 0xcf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x42966c68);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01c7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s5, gas - 1)
      else
        ExecuteFromCFGNode_s224(s5, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 21
    * Starting at 0xda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x67916e17);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01dc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s238(s5, gas - 1)
      else
        ExecuteFromCFGNode_s225(s5, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 22
    * Starting at 0xe5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ef);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s227(s5, gas - 1)
      else
        ExecuteFromCFGNode_s226(s5, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 23
    * Starting at 0xf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x012c);
      assert s1.Peek(0) == 0x12c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s2, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 50
    * Starting at 0x1ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0177);
      var s3 := Push2(s2, 0x01fd);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0aad);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s7, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 185
    * Starting at 0xaad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1fd

    requires s0.stack[3] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fd;
      assert s1.Peek(3) == 0x177;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0abe);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s10, gas - 1)
      else
        ExecuteFromCFGNode_s229(s10, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 186
    * Starting at 0xabb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1fd

    requires s0.stack[4] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x1fd;
      assert s1.Peek(5) == 0x177;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 230
    * Segment Id for this node is: 187
    * Starting at 0xabe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1fd

    requires s0.stack[4] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1fd;
      assert s1.Peek(4) == 0x177;
      var s2 := Push2(s1, 0x0ac7);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s5, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0xac7

    requires s0.stack[5] == 0x1fd

    requires s0.stack[6] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xac7;
      assert s1.Peek(5) == 0x1fd;
      assert s1.Peek(6) == 0x177;
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
      assert s11.Peek(4) == 0xac7;
      assert s11.Peek(8) == 0x1fd;
      assert s11.Peek(9) == 0x177;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s14, gas - 1)
      else
        ExecuteFromCFGNode_s232(s14, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xac7

    requires s0.stack[6] == 0x1fd

    requires s0.stack[7] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xac7;
      assert s1.Peek(7) == 0x1fd;
      assert s1.Peek(8) == 0x177;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 233
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xac7

    requires s0.stack[6] == 0x1fd

    requires s0.stack[7] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac7;
      assert s1.Peek(6) == 0x1fd;
      assert s1.Peek(7) == 0x177;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s5, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 188
    * Starting at 0xac7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1fd

    requires s0.stack[5] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1fd;
      assert s1.Peek(5) == 0x177;
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
    * Segment Id for this node is: 51
    * Starting at 0x1fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x177;
      var s2 := Push2(s1, 0x04b4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s3, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 102
    * Starting at 0x4b4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x177;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x177;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s237(s19, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x177;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s5, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 48
    * Starting at 0x1dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01da);
      var s3 := Push2(s2, 0x01ea);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0b64);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s7, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 203
    * Starting at 0xb64
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1ea

    requires s0.stack[3] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ea;
      assert s1.Peek(3) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x80);
      var s7 := Dup6(s6);
      var s8 := Dup8(s7);
      var s9 := Sub(s8);
      var s10 := SLt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(7) == 0x1ea;
      assert s11.Peek(8) == 0x1da;
      var s12 := Push2(s11, 0x0b79);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s13, gas - 1)
      else
        ExecuteFromCFGNode_s240(s13, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 204
    * Starting at 0xb76
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1ea

    requires s0.stack[7] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(7) == 0x1ea;
      assert s1.Peek(8) == 0x1da;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 241
    * Segment Id for this node is: 205
    * Starting at 0xb79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1ea

    requires s0.stack[7] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1ea;
      assert s1.Peek(7) == 0x1da;
      var s2 := Push2(s1, 0x0b82);
      var s3 := Dup6(s2);
      var s4 := Push2(s3, 0x0a9d);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s5, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 183
    * Starting at 0xa9d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xb82

    requires s0.stack[8] == 0x1ea

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb82;
      assert s1.Peek(8) == 0x1ea;
      assert s1.Peek(9) == 0x1da;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x04ce);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s244(s10, gas - 1)
      else
        ExecuteFromCFGNode_s243(s10, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 184
    * Starting at 0xaa9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xb82

    requires s0.stack[9] == 0x1ea

    requires s0.stack[10] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xb82;
      assert s1.Peek(10) == 0x1ea;
      assert s1.Peek(11) == 0x1da;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 244
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xb82

    requires s0.stack[9] == 0x1ea

    requires s0.stack[10] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb82;
      assert s1.Peek(9) == 0x1ea;
      assert s1.Peek(10) == 0x1da;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s5, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 206
    * Starting at 0xb82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x1ea

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1ea;
      assert s1.Peek(8) == 0x1da;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0b90);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a9d);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s9, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 183
    * Starting at 0xa9d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xb90

    requires s0.stack[8] == 0x1ea

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb90;
      assert s1.Peek(8) == 0x1ea;
      assert s1.Peek(9) == 0x1da;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x04ce);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s10, gas - 1)
      else
        ExecuteFromCFGNode_s247(s10, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 184
    * Starting at 0xaa9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xb90

    requires s0.stack[9] == 0x1ea

    requires s0.stack[10] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xb90;
      assert s1.Peek(10) == 0x1ea;
      assert s1.Peek(11) == 0x1da;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 248
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xb90

    requires s0.stack[9] == 0x1ea

    requires s0.stack[10] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb90;
      assert s1.Peek(9) == 0x1ea;
      assert s1.Peek(10) == 0x1da;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s5, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 207
    * Starting at 0xb90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x1ea

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1ea;
      assert s1.Peek(8) == 0x1da;
      var s2 := Swap4(s1);
      var s3 := Swap7(s2);
      var s4 := Swap4(s3);
      var s5 := Swap6(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup3(s10);
      assert s11.Peek(2) == 0x1ea;
      assert s11.Peek(6) == 0x1da;
      var s12 := Add(s11);
      var s13 := CallDataLoad(s12);
      var s14 := Swap2(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Add(s15);
      var s17 := CallDataLoad(s16);
      var s18 := Swap1(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s19, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 49
    * Starting at 0x1ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1da;
      var s2 := Push2(s1, 0x0445);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s3, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 97
    * Starting at 0x445
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x445 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1da;
      var s2 := Push2(s1, 0x044d);
      var s3 := Push2(s2, 0x067f);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s4, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x44d

    requires s0.stack[5] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x44d;
      assert s1.Peek(5) == 0x1da;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s4, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 98
    * Starting at 0x44d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push2(s7, 0x045e);
      var s9 := Push2(s8, 0x053b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s10, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x45e

    requires s0.stack[6] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x45e;
      assert s1.Peek(6) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s11, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 99
    * Starting at 0x45e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0484);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s10, gas - 1)
      else
        ExecuteFromCFGNode_s256(s10, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 100
    * Starting at 0x46d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x1da;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(6) == 0x1da;
      var s12 := Push2(s11, 0x0dea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s13, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 226
    * Starting at 0xdea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x3b7

    requires s0.stack[6] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(6) == 0x1da;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Dup2(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push32(s9, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x3b7;
      assert s11.Peek(8) == 0x1da;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s18, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1da;
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

  /** Node 259
    * Segment Id for this node is: 101
    * Starting at 0x484
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x484 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1da;
      var s2 := Push1(s1, 0x06);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0xff);
      var s6 := Not(s5);
      var s7 := And(s6);
      var s8 := Swap5(s7);
      var s9 := IsZero(s8);
      var s10 := IsZero(s9);
      var s11 := Swap5(s10);
      assert s11.Peek(6) == 0x1da;
      var s12 := Swap1(s11);
      var s13 := Swap5(s12);
      var s14 := Or(s13);
      var s15 := Push2(s14, 0xff00);
      var s16 := Not(s15);
      var s17 := And(s16);
      var s18 := Push2(s17, 0x0100);
      var s19 := Swap4(s18);
      var s20 := IsZero(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(6) == 0x1da;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := Mul(s24);
      var s26 := Swap3(s25);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := Or(s28);
      var s30 := Swap1(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(4) == 0x1da;
      var s32 := SStore(s31);
      var s33 := Push1(s32, 0x07);
      var s34 := Swap2(s33);
      var s35 := Swap1(s34);
      var s36 := Swap2(s35);
      var s37 := SStore(s36);
      var s38 := Push1(s37, 0x08);
      var s39 := SStore(s38);
      var s40 := Jump(s39);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s40, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 45
    * Starting at 0x1c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01da);
      var s3 := Push2(s2, 0x01d5);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0ba5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s7, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 208
    * Starting at 0xba5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1d5

    requires s0.stack[3] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d5;
      assert s1.Peek(3) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0bb6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s10, gas - 1)
      else
        ExecuteFromCFGNode_s262(s10, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 209
    * Starting at 0xbb3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1d5

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x1d5;
      assert s1.Peek(5) == 0x1da;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 263
    * Segment Id for this node is: 210
    * Starting at 0xbb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1d5

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1d5;
      assert s1.Peek(4) == 0x1da;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s7, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 46
    * Starting at 0x1d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
      var s2 := Push2(s1, 0x0438);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s3, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 95
    * Starting at 0x438
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x438 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1da;
      var s2 := Push2(s1, 0x0442);
      var s3 := Caller(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0861);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s6, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 152
    * Starting at 0x861
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x861 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x442

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x442;
      assert s1.Peek(4) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0887);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s270(s10, gas - 1)
      else
        ExecuteFromCFGNode_s267(s10, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 153
    * Starting at 0x870
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x870 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x442

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x442;
      assert s1.Peek(5) == 0x1da;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(4) == 0x442;
      assert s11.Peek(6) == 0x1da;
      var s12 := Push2(s11, 0x0e1f);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s13, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 227
    * Starting at 0xe1f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x3b7

    requires s0.stack[4] == 0x442

    requires s0.stack[6] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(4) == 0x442;
      assert s1.Peek(6) == 0x1da;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x21);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a206275726e2066726f6d20746865207a65726f20616464726573);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(5) == 0x442;
      assert s11.Peek(7) == 0x1da;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x73);
      var s17 := Push1(s16, 0xf8);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(6) == 0x442;
      assert s21.Peek(8) == 0x1da;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s26, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x442

    requires s0.stack[5] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x442;
      assert s1.Peek(5) == 0x1da;
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

  /** Node 270
    * Segment Id for this node is: 154
    * Starting at 0x887
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x887 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x442

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x442;
      assert s1.Peek(4) == 0x1da;
      var s2 := Push2(s1, 0x0893);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09a3);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s7, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 162
    * Starting at 0x9a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x893

    requires s0.stack[6] == 0x442

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x893;
      assert s1.Peek(6) == 0x442;
      assert s1.Peek(8) == 0x1da;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0a12);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s298(s10, gas - 1)
      else
        ExecuteFromCFGNode_s272(s10, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 163
    * Starting at 0x9b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x893

    requires s0.stack[6] == 0x442

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09ba);
      assert s1.Peek(0) == 0x9ba;
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Push2(s1, 0x053b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s3, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x9ba

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9ba;
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s11, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 164
    * Starting at 0x9ba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(8) == 0x893;
      assert s11.Peek(11) == 0x442;
      assert s11.Peek(13) == 0x1da;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := Dup1(s15);
      var s17 := Push2(s16, 0x09f1);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s278(s18, gas - 1)
      else
        ExecuteFromCFGNode_s275(s18, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 165
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x893;
      assert s1.Peek(6) == 0x442;
      assert s1.Peek(8) == 0x1da;
      var s2 := Push2(s1, 0x09dc);
      var s3 := Push2(s2, 0x053b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s4, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x9dc

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9dc;
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s11, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 166
    * Starting at 0x9dc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup3(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(8) == 0x893;
      assert s11.Peek(11) == 0x442;
      assert s11.Peek(13) == 0x1da;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s278(s15, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 167
    * Starting at 0x9f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Push2(s1, 0x0a0d);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s282(s3, gas - 1)
      else
        ExecuteFromCFGNode_s279(s3, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 168
    * Starting at 0x9f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x893

    requires s0.stack[6] == 0x442

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x893;
      assert s11.Peek(8) == 0x442;
      assert s11.Peek(10) == 0x1da;
      var s12 := Push2(s11, 0x0e60);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s13, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 228
    * Starting at 0xe60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x893

    requires s0.stack[8] == 0x442

    requires s0.stack[10] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x893;
      assert s1.Peek(8) == 0x442;
      assert s1.Peek(10) == 0x1da;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x16);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 22, 0x1d1c98591a5b99c81a5cc81b9bdd081cdd185c9d1959);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x893;
      assert s11.Peek(9) == 0x442;
      assert s11.Peek(11) == 0x1da;
      var s12 := Push1(s11, 0x52);
      var s13 := Shl(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s21, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
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

  /** Node 282
    * Segment Id for this node is: 169
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x893

    requires s0.stack[6] == 0x442

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x893;
      assert s1.Peek(6) == 0x442;
      assert s1.Peek(8) == 0x1da;
      var s2 := Push2(s1, 0x094e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s3, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 160
    * Starting at 0x94e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x893

    requires s0.stack[6] == 0x442

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x893;
      assert s1.Peek(6) == 0x442;
      assert s1.Peek(8) == 0x1da;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s5, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 155
    * Starting at 0x893
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x893 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x442

    requires s0.stack[4] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x442;
      assert s1.Peek(4) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x442;
      assert s11.Peek(7) == 0x1da;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup2(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0x442;
      assert s21.Peek(7) == 0x1da;
      var s22 := Lt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x08cc);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s288(s25, gas - 1)
      else
        ExecuteFromCFGNode_s285(s25, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 156
    * Starting at 0x8b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x442

    requires s0.stack[5] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x442;
      assert s1.Peek(6) == 0x1da;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x442;
      assert s11.Peek(7) == 0x1da;
      var s12 := Push2(s11, 0x0c72);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s13, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 220
    * Starting at 0xc72
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x442

    requires s0.stack[7] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x442;
      assert s1.Peek(7) == 0x1da;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a206275726e20616d6f756e7420657863656564732062616c616e);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x442;
      assert s11.Peek(8) == 0x1da;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x6365);
      var s17 := Push1(s16, 0xf0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x442;
      assert s21.Peek(9) == 0x1da;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s26, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x442

    requires s0.stack[6] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x442;
      assert s1.Peek(6) == 0x1da;
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

  /** Node 288
    * Segment Id for this node is: 157
    * Starting at 0x8cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x442

    requires s0.stack[5] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x442;
      assert s1.Peek(5) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x442;
      assert s11.Peek(8) == 0x1da;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Dup2(s16);
      var s18 := Keccak256(s17);
      var s19 := Dup4(s18);
      var s20 := Dup4(s19);
      var s21 := Sub(s20);
      assert s21.Peek(6) == 0x442;
      assert s21.Peek(8) == 0x1da;
      var s22 := Swap1(s21);
      var s23 := SStore(s22);
      var s24 := Push1(s23, 0x03);
      var s25 := Dup1(s24);
      var s26 := SLoad(s25);
      var s27 := Dup5(s26);
      var s28 := Swap3(s27);
      var s29 := Swap1(s28);
      var s30 := Push2(s29, 0x08fb);
      var s31 := Swap1(s30);
      assert s31.Peek(1) == 0x8fb;
      assert s31.Peek(8) == 0x442;
      assert s31.Peek(10) == 0x1da;
      var s32 := Dup5(s31);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0f8d);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s35, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 237
    * Starting at 0xf8d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x8fb

    requires s0.stack[9] == 0x442

    requires s0.stack[11] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8fb;
      assert s1.Peek(9) == 0x442;
      assert s1.Peek(11) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0f9f);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s292(s8, gas - 1)
      else
        ExecuteFromCFGNode_s290(s8, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 238
    * Starting at 0xf98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8fb

    requires s0.stack[10] == 0x442

    requires s0.stack[12] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f9f);
      assert s1.Peek(0) == 0xf9f;
      assert s1.Peek(4) == 0x8fb;
      assert s1.Peek(11) == 0x442;
      assert s1.Peek(13) == 0x1da;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s3, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xf9f

    requires s0.stack[4] == 0x8fb

    requires s0.stack[11] == 0x442

    requires s0.stack[13] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf9f;
      assert s1.Peek(4) == 0x8fb;
      assert s1.Peek(11) == 0x442;
      assert s1.Peek(13) == 0x1da;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf9f;
      assert s11.Peek(6) == 0x8fb;
      assert s11.Peek(13) == 0x442;
      assert s11.Peek(15) == 0x1da;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 292
    * Segment Id for this node is: 239
    * Starting at 0xf9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8fb

    requires s0.stack[10] == 0x442

    requires s0.stack[12] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8fb;
      assert s1.Peek(10) == 0x442;
      assert s1.Peek(12) == 0x1da;
      var s2 := Pop(s1);
      var s3 := Sub(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s293(s5, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 158
    * Starting at 0x8fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(6) == 0x442;
      assert s11.Peek(8) == 0x1da;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := Dup6(s15);
      var s17 := And(s16);
      var s18 := Swap1(s17);
      var s19 := Push32(s18, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s20 := Swap1(s19);
      var s21 := Push2(s20, 0x093e);
      assert s21.Peek(0) == 0x93e;
      assert s21.Peek(8) == 0x442;
      assert s21.Peek(10) == 0x1da;
      var s22 := Swap1(s21);
      var s23 := Dup7(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x0f5e);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s294(s26, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 232
    * Starting at 0xf5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x93e

    requires s0.stack[9] == 0x442

    requires s0.stack[11] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x93e;
      assert s1.Peek(9) == 0x442;
      assert s1.Peek(11) == 0x1da;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s8, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 159
    * Starting at 0x93e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x094e);
      var s10 := Dup4(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x94e;
      assert s11.Peek(6) == 0x442;
      assert s11.Peek(8) == 0x1da;
      var s12 := Dup5(s11);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s296(s12, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 160
    * Starting at 0x94e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x94e

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x94e;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s5, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 160
    * Starting at 0x94e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x442

    requires s0.stack[5] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x442;
      assert s1.Peek(5) == 0x1da;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 170
    * Starting at 0xa12
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x893

    requires s0.stack[6] == 0x442

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x893;
      assert s1.Peek(6) == 0x442;
      assert s1.Peek(8) == 0x1da;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a2b);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s300(s9, gas - 1)
      else
        ExecuteFromCFGNode_s299(s9, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 171
    * Starting at 0xa1f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x893;
      assert s1.Peek(6) == 0x442;
      assert s1.Peek(8) == 0x1da;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := And(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s300(s8, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 172
    * Starting at 0xa2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x094e);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s283(s4, gas - 1)
      else
        ExecuteFromCFGNode_s301(s4, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 173
    * Starting at 0xa31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x893

    requires s0.stack[6] == 0x442

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x07);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0a3d);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x04b4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s7, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 102
    * Starting at 0x4b4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xa3d

    requires s0.stack[7] == 0x893

    requires s0.stack[10] == 0x442

    requires s0.stack[12] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa3d;
      assert s1.Peek(7) == 0x893;
      assert s1.Peek(10) == 0x442;
      assert s1.Peek(12) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0xa3d;
      assert s11.Peek(10) == 0x893;
      assert s11.Peek(13) == 0x442;
      assert s11.Peek(15) == 0x1da;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s303(s19, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xa3d

    requires s0.stack[8] == 0x893

    requires s0.stack[11] == 0x442

    requires s0.stack[13] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa3d;
      assert s1.Peek(8) == 0x893;
      assert s1.Peek(11) == 0x442;
      assert s1.Peek(13) == 0x1da;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s5, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 174
    * Starting at 0xa3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x893

    requires s0.stack[9] == 0x442

    requires s0.stack[11] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x893;
      assert s1.Peek(9) == 0x442;
      assert s1.Peek(11) == 0x1da;
      var s2 := Push2(s1, 0x0a47);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0f75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s305(s6, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xa47

    requires s0.stack[7] == 0x893

    requires s0.stack[10] == 0x442

    requires s0.stack[12] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa47;
      assert s1.Peek(7) == 0x893;
      assert s1.Peek(10) == 0x442;
      assert s1.Peek(12) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s308(s9, gas - 1)
      else
        ExecuteFromCFGNode_s306(s9, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa47

    requires s0.stack[8] == 0x893

    requires s0.stack[11] == 0x442

    requires s0.stack[13] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa47;
      assert s1.Peek(9) == 0x893;
      assert s1.Peek(12) == 0x442;
      assert s1.Peek(14) == 0x1da;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s3, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0xa47

    requires s0.stack[9] == 0x893

    requires s0.stack[12] == 0x442

    requires s0.stack[14] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa47;
      assert s1.Peek(9) == 0x893;
      assert s1.Peek(12) == 0x442;
      assert s1.Peek(14) == 0x1da;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0xa47;
      assert s11.Peek(11) == 0x893;
      assert s11.Peek(14) == 0x442;
      assert s11.Peek(16) == 0x1da;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 308
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa47

    requires s0.stack[8] == 0x893

    requires s0.stack[11] == 0x442

    requires s0.stack[13] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa47;
      assert s1.Peek(8) == 0x893;
      assert s1.Peek(11) == 0x442;
      assert s1.Peek(13) == 0x1da;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s5, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 175
    * Starting at 0xa47
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa47 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x893

    requires s0.stack[8] == 0x442

    requires s0.stack[10] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x893;
      assert s1.Peek(8) == 0x442;
      assert s1.Peek(10) == 0x1da;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a6a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s319(s7, gas - 1)
      else
        ExecuteFromCFGNode_s310(s7, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 176
    * Starting at 0xa50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x893;
      assert s1.Peek(6) == 0x442;
      assert s1.Peek(8) == 0x1da;
      var s2 := Push1(s1, 0x08);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x0a5d);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x04b4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s8, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 102
    * Starting at 0x4b4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xa5d

    requires s0.stack[7] == 0x893

    requires s0.stack[10] == 0x442

    requires s0.stack[12] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa5d;
      assert s1.Peek(7) == 0x893;
      assert s1.Peek(10) == 0x442;
      assert s1.Peek(12) == 0x1da;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0xa5d;
      assert s11.Peek(10) == 0x893;
      assert s11.Peek(13) == 0x442;
      assert s11.Peek(15) == 0x1da;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s312(s19, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xa5d

    requires s0.stack[8] == 0x893

    requires s0.stack[11] == 0x442

    requires s0.stack[13] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa5d;
      assert s1.Peek(8) == 0x893;
      assert s1.Peek(11) == 0x442;
      assert s1.Peek(13) == 0x1da;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s5, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 177
    * Starting at 0xa5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x893

    requires s0.stack[9] == 0x442

    requires s0.stack[11] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x893;
      assert s1.Peek(9) == 0x442;
      assert s1.Peek(11) == 0x1da;
      var s2 := Push2(s1, 0x0a67);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0f75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s314(s6, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xa67

    requires s0.stack[7] == 0x893

    requires s0.stack[10] == 0x442

    requires s0.stack[12] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa67;
      assert s1.Peek(7) == 0x893;
      assert s1.Peek(10) == 0x442;
      assert s1.Peek(12) == 0x1da;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s317(s9, gas - 1)
      else
        ExecuteFromCFGNode_s315(s9, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa67

    requires s0.stack[8] == 0x893

    requires s0.stack[11] == 0x442

    requires s0.stack[13] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa67;
      assert s1.Peek(9) == 0x893;
      assert s1.Peek(12) == 0x442;
      assert s1.Peek(14) == 0x1da;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s3, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0xa67

    requires s0.stack[9] == 0x893

    requires s0.stack[12] == 0x442

    requires s0.stack[14] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa67;
      assert s1.Peek(9) == 0x893;
      assert s1.Peek(12) == 0x442;
      assert s1.Peek(14) == 0x1da;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0xa67;
      assert s11.Peek(11) == 0x893;
      assert s11.Peek(14) == 0x442;
      assert s11.Peek(16) == 0x1da;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 317
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa67

    requires s0.stack[8] == 0x893

    requires s0.stack[11] == 0x442

    requires s0.stack[13] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa67;
      assert s1.Peek(8) == 0x893;
      assert s1.Peek(11) == 0x442;
      assert s1.Peek(13) == 0x1da;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s5, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 178
    * Starting at 0xa67
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x893

    requires s0.stack[8] == 0x442

    requires s0.stack[10] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x893;
      assert s1.Peek(8) == 0x442;
      assert s1.Peek(10) == 0x1da;
      var s2 := Lt(s1);
      var s3 := IsZero(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s319(s3, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 179
    * Starting at 0xa6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x893

    requires s0.stack[7] == 0x442

    requires s0.stack[9] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := Push2(s1, 0x094e);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s283(s3, gas - 1)
      else
        ExecuteFromCFGNode_s320(s3, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 180
    * Starting at 0xa6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x893

    requires s0.stack[6] == 0x442

    requires s0.stack[8] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(7) == 0x442;
      assert s1.Peek(9) == 0x1da;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x893;
      assert s11.Peek(8) == 0x442;
      assert s11.Peek(10) == 0x1da;
      var s12 := Push2(s11, 0x0d82);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s13, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 224
    * Starting at 0xd82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x893

    requires s0.stack[8] == 0x442

    requires s0.stack[10] == 0x1da

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x893;
      assert s1.Peek(8) == 0x442;
      assert s1.Peek(10) == 0x1da;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x06);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 6, 0x119bdc989a59);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x893;
      assert s11.Peek(9) == 0x442;
      assert s11.Peek(11) == 0x1da;
      var s12 := Push1(s11, 0xd2);
      var s13 := Shl(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s21, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 43
    * Starting at 0x1b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0162);
      var s3 := Push2(s2, 0x01c2);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0b3b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s7, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 199
    * Starting at 0xb3b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1c2

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c2;
      assert s1.Peek(3) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0b4d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s325(s11, gas - 1)
      else
        ExecuteFromCFGNode_s324(s11, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 200
    * Starting at 0xb4a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c2

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x1c2;
      assert s1.Peek(6) == 0x162;
      var s2 := Dup3(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 325
    * Segment Id for this node is: 201
    * Starting at 0xb4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c2

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1c2;
      assert s1.Peek(5) == 0x162;
      var s2 := Push2(s1, 0x0b56);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s5, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb56

    requires s0.stack[6] == 0x1c2

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb56;
      assert s1.Peek(6) == 0x1c2;
      assert s1.Peek(7) == 0x162;
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
      assert s11.Peek(4) == 0xb56;
      assert s11.Peek(9) == 0x1c2;
      assert s11.Peek(10) == 0x162;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s328(s14, gas - 1)
      else
        ExecuteFromCFGNode_s327(s14, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb56

    requires s0.stack[7] == 0x1c2

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xb56;
      assert s1.Peek(8) == 0x1c2;
      assert s1.Peek(9) == 0x162;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 328
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb56

    requires s0.stack[7] == 0x1c2

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb56;
      assert s1.Peek(7) == 0x1c2;
      assert s1.Peek(8) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s329(s5, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 202
    * Starting at 0xb56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1c2

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1c2;
      assert s1.Peek(6) == 0x162;
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
      assert s11.Peek(1) == 0x1c2;
      assert s11.Peek(4) == 0x162;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s13, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 44
    * Starting at 0x1c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      var s2 := Push2(s1, 0x03e4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s331(s3, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 90
    * Starting at 0x3e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0331);
      var s4 := Push2(s3, 0x03f1);
      var s5 := Push2(s4, 0x067f);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s6, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x3f1

    requires s0.stack[1] == 0x331

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3f1;
      assert s1.Peek(1) == 0x331;
      assert s1.Peek(5) == 0x162;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s333(s4, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 91
    * Starting at 0x3f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x331

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x331;
      assert s1.Peek(5) == 0x162;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x03ff);
      var s7 := Push2(s6, 0x067f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s8, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x3ff

    requires s0.stack[6] == 0x331

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3ff;
      assert s1.Peek(6) == 0x331;
      assert s1.Peek(10) == 0x162;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s4, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 92
    * Starting at 0x3ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x331

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x331;
      assert s1.Peek(10) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Dup3(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(10) == 0x162;
      var s12 := Push1(s11, 0x20);
      var s13 := Dup1(s12);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Swap2(s20);
      assert s21.Peek(7) == 0x331;
      assert s21.Peek(11) == 0x162;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := Push1(s23, 0x00);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := Keccak256(s26);
      var s28 := Swap2(s27);
      var s29 := Dup12(s28);
      var s30 := And(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x331;
      assert s31.Peek(13) == 0x162;
      var s32 := MStore(s31);
      var s33 := Swap3(s32);
      var s34 := MStore(s33);
      var s35 := Swap1(s34);
      var s36 := Keccak256(s35);
      var s37 := SLoad(s36);
      var s38 := Push2(s37, 0x0433);
      var s39 := Swap2(s38);
      var s40 := Swap1(s39);
      var s41 := Push2(s40, 0x0f75);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s336(s41, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 93
    * Starting at 0x432
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x432 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0xf75

    requires s0.stack[3] == 0x433

    requires s0.stack[6] == 0x331

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s1, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x433

    requires s0.stack[5] == 0x331

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x433;
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(9) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s340(s9, gas - 1)
      else
        ExecuteFromCFGNode_s338(s9, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x433

    requires s0.stack[6] == 0x331

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0x433;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s3, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0x433

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0x433;
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0x433;
      assert s11.Peek(9) == 0x331;
      assert s11.Peek(13) == 0x162;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 340
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x433

    requires s0.stack[6] == 0x331

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x433;
      assert s1.Peek(6) == 0x331;
      assert s1.Peek(10) == 0x162;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s5, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 94
    * Starting at 0x433
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x433 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(7) == 0x162;
      var s2 := Push2(s1, 0x0683);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s3, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 133
    * Starting at 0x683
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(7) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06a9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s345(s10, gas - 1)
      else
        ExecuteFromCFGNode_s343(s10, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 134
    * Starting at 0x692
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x692 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x331;
      assert s11.Peek(9) == 0x162;
      var s12 := Push2(s11, 0x0ed5);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s13, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 230
    * Starting at 0xed5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x331

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(9) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x24);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(10) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push4(s15, 0x72657373);
      var s17 := Push1(s16, 0xe0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x331;
      assert s21.Peek(11) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s26, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 135
    * Starting at 0x6a9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(7) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06cf);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s348(s10, gas - 1)
      else
        ExecuteFromCFGNode_s346(s10, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 136
    * Starting at 0x6b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x331;
      assert s11.Peek(9) == 0x162;
      var s12 := Push2(s11, 0x0cfa);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s13, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 222
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x331

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(9) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(10) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x7373);
      var s17 := Push1(s16, 0xf0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x331;
      assert s21.Peek(11) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s26, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 137
    * Starting at 0x6cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x331

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(7) == 0x162;
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
      assert s11.Peek(7) == 0x331;
      assert s11.Peek(11) == 0x162;
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
      assert s21.Peek(10) == 0x331;
      assert s21.Peek(14) == 0x162;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Dup8(s23);
      var s25 := And(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := MStore(s27);
      var s29 := Swap5(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(9) == 0x331;
      assert s31.Peek(13) == 0x162;
      var s32 := MStore(s31);
      var s33 := Swap1(s32);
      var s34 := Dup2(s33);
      var s35 := Swap1(s34);
      var s36 := Keccak256(s35);
      var s37 := Dup5(s36);
      var s38 := Swap1(s37);
      var s39 := SStore(s38);
      var s40 := MLoad(s39);
      var s41 := Push32(s40, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s349(s41, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 138
    * Starting at 0x71f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
      var s2 := Push2(s1, 0x072a);
      var s3 := Swap1(s2);
      var s4 := Dup6(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0f5e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s7, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 232
    * Starting at 0xf5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x72a

    requires s0.stack[9] == 0x331

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x72a;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(13) == 0x162;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s8, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 139
    * Starting at 0x72a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x331

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x331;
      assert s1.Peek(11) == 0x162;
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
      assert s11.Peek(0) == 0x331;
      assert s11.Peek(4) == 0x162;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s12, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 41
    * Starting at 0x19f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01a7);
      var s3 := Push2(s2, 0x03df);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s4, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 89
    * Starting at 0x3df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1a7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a7;
      var s2 := Push1(s1, 0x12);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s4, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 42
    * Starting at 0x1a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0146);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0f67);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s8, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 233
    * Starting at 0xf67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x146;
      var s2 := Push1(s1, 0xff);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Swap2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(0) == 0x146;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s12, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 24
    * Starting at 0xf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf4 as nat
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
      var s5 := Push2(s4, 0x0131);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s472(s6, gas - 1)
      else
        ExecuteFromCFGNode_s357(s6, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 25
    * Starting at 0x100
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x014f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s460(s5, gas - 1)
      else
        ExecuteFromCFGNode_s358(s5, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 26
    * Starting at 0x10b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x016f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s458(s5, gas - 1)
      else
        ExecuteFromCFGNode_s359(s5, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 27
    * Starting at 0x116
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1ab99e12);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0184);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s456(s5, gas - 1)
      else
        ExecuteFromCFGNode_s360(s5, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 28
    * Starting at 0x121
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x018c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s361(s5, gas - 1)
      else
        ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 39
    * Starting at 0x18c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0162);
      var s3 := Push2(s2, 0x019a);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0b00);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s7, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 194
    * Starting at 0xb00
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x19a

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x19a;
      assert s1.Peek(3) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0b14);
      assert s11.Peek(0) == 0xb14;
      assert s11.Peek(7) == 0x19a;
      assert s11.Peek(8) == 0x162;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s364(s12, gas - 1)
      else
        ExecuteFromCFGNode_s363(s12, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 195
    * Starting at 0xb11
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x19a

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(6) == 0x19a;
      assert s1.Peek(7) == 0x162;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 364
    * Segment Id for this node is: 196
    * Starting at 0xb14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x19a

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x19a;
      assert s1.Peek(6) == 0x162;
      var s2 := Push2(s1, 0x0b1d);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s5, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xb1d

    requires s0.stack[7] == 0x19a

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb1d;
      assert s1.Peek(7) == 0x19a;
      assert s1.Peek(8) == 0x162;
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
      assert s11.Peek(4) == 0xb1d;
      assert s11.Peek(10) == 0x19a;
      assert s11.Peek(11) == 0x162;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s367(s14, gas - 1)
      else
        ExecuteFromCFGNode_s366(s14, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xb1d

    requires s0.stack[8] == 0x19a

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xb1d;
      assert s1.Peek(9) == 0x19a;
      assert s1.Peek(10) == 0x162;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 367
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xb1d

    requires s0.stack[8] == 0x19a

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb1d;
      assert s1.Peek(8) == 0x19a;
      assert s1.Peek(9) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s5, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 197
    * Starting at 0xb1d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x19a

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x19a;
      assert s1.Peek(7) == 0x162;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0b2b);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a86);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s9, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xb2b

    requires s0.stack[7] == 0x19a

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2b;
      assert s1.Peek(7) == 0x19a;
      assert s1.Peek(8) == 0x162;
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
      assert s11.Peek(4) == 0xb2b;
      assert s11.Peek(10) == 0x19a;
      assert s11.Peek(11) == 0x162;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s371(s14, gas - 1)
      else
        ExecuteFromCFGNode_s370(s14, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xb2b

    requires s0.stack[8] == 0x19a

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xb2b;
      assert s1.Peek(9) == 0x19a;
      assert s1.Peek(10) == 0x162;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 371
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xb2b

    requires s0.stack[8] == 0x19a

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb2b;
      assert s1.Peek(8) == 0x19a;
      assert s1.Peek(9) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s5, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 198
    * Starting at 0xb2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x19a

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x19a;
      assert s1.Peek(7) == 0x162;
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
      assert s11.Peek(4) == 0x19a;
      assert s11.Peek(5) == 0x162;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Swap3(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s15, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 40
    * Starting at 0x19a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x162;
      var s2 := Push2(s1, 0x0346);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s3, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 81
    * Starting at 0x346
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0353);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0737);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s8, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 140
    * Starting at 0x737
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x737 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x353

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x353;
      assert s1.Peek(8) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x075d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s379(s10, gas - 1)
      else
        ExecuteFromCFGNode_s376(s10, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 141
    * Starting at 0x746
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x746 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x353

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x353;
      assert s1.Peek(9) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x353;
      assert s11.Peek(10) == 0x162;
      var s12 := Push2(s11, 0x0e90);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s13, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 229
    * Starting at 0xe90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x353

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x353;
      assert s1.Peek(10) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x25);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x353;
      assert s11.Peek(11) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 5, 0x6472657373);
      var s17 := Push1(s16, 0xd8);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x353;
      assert s21.Peek(12) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s26, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x353

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x353;
      assert s1.Peek(9) == 0x162;
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

  /** Node 379
    * Segment Id for this node is: 142
    * Starting at 0x75d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x353

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x353;
      assert s1.Peek(8) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0783);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s382(s10, gas - 1)
      else
        ExecuteFromCFGNode_s380(s10, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 143
    * Starting at 0x76c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x353

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x353;
      assert s1.Peek(9) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x353;
      assert s11.Peek(10) == 0x162;
      var s12 := Push2(s11, 0x0c2f);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s13, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 219
    * Starting at 0xc2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x353

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x353;
      assert s1.Peek(10) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x23);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x353;
      assert s11.Peek(11) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push3(s15, 0x657373);
      var s17 := Push1(s16, 0xe8);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x353;
      assert s21.Peek(12) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s26, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 144
    * Starting at 0x783
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x353

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x353;
      assert s1.Peek(8) == 0x162;
      var s2 := Push2(s1, 0x078e);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09a3);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s7, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 162
    * Starting at 0x9a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x353

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0a12);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s432(s10, gas - 1)
      else
        ExecuteFromCFGNode_s384(s10, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 163
    * Starting at 0x9b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x353

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09ba);
      assert s1.Peek(0) == 0x9ba;
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Push2(s1, 0x053b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s3, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x9ba

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9ba;
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s11, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 164
    * Starting at 0x9ba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(8) == 0x78e;
      assert s11.Peek(12) == 0x353;
      assert s11.Peek(17) == 0x162;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := Dup1(s15);
      var s17 := Push2(s16, 0x09f1);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s390(s18, gas - 1)
      else
        ExecuteFromCFGNode_s387(s18, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 165
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(12) == 0x162;
      var s2 := Push2(s1, 0x09dc);
      var s3 := Push2(s2, 0x053b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s388(s4, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 113
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x9dc

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9dc;
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s389(s11, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 166
    * Starting at 0x9dc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup3(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(8) == 0x78e;
      assert s11.Peek(12) == 0x353;
      assert s11.Peek(17) == 0x162;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s390(s15, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 167
    * Starting at 0x9f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Push2(s1, 0x0a0d);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s394(s3, gas - 1)
      else
        ExecuteFromCFGNode_s391(s3, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 168
    * Starting at 0x9f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x353

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x78e;
      assert s11.Peek(9) == 0x353;
      assert s11.Peek(14) == 0x162;
      var s12 := Push2(s11, 0x0e60);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s13, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 228
    * Starting at 0xe60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x78e

    requires s0.stack[9] == 0x353

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x78e;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(14) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x16);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 22, 0x1d1c98591a5b99c81a5cc81b9bdd081cdd185c9d1959);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x78e;
      assert s11.Peek(10) == 0x353;
      assert s11.Peek(15) == 0x162;
      var s12 := Push1(s11, 0x52);
      var s13 := Shl(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s21, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
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

  /** Node 394
    * Segment Id for this node is: 169
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x353

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(12) == 0x162;
      var s2 := Push2(s1, 0x094e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s3, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 160
    * Starting at 0x94e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x353

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(12) == 0x162;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s5, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 145
    * Starting at 0x78e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x353

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x353;
      assert s1.Peek(8) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x353;
      assert s11.Peek(11) == 0x162;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup2(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x353;
      assert s21.Peek(11) == 0x162;
      var s22 := Lt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x07c7);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s400(s25, gas - 1)
      else
        ExecuteFromCFGNode_s397(s25, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 146
    * Starting at 0x7b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x353

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x353;
      assert s1.Peek(10) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(6) == 0x353;
      assert s11.Peek(11) == 0x162;
      var s12 := Push2(s11, 0x0d3c);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s13, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 223
    * Starting at 0xd3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x3b7

    requires s0.stack[6] == 0x353

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(6) == 0x353;
      assert s1.Peek(11) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x26);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(7) == 0x353;
      assert s11.Peek(12) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 6, 0x616c616e6365);
      var s17 := Push1(s16, 0xd0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(8) == 0x353;
      assert s21.Peek(13) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s399(s26, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x353

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x353;
      assert s1.Peek(10) == 0x162;
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

  /** Node 400
    * Segment Id for this node is: 147
    * Starting at 0x7c7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x353

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x353;
      assert s1.Peek(9) == 0x162;
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
      assert s11.Peek(7) == 0x353;
      assert s11.Peek(12) == 0x162;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Keccak256(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(9) == 0x353;
      assert s21.Peek(14) == 0x162;
      var s22 := Dup6(s21);
      var s23 := Sub(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Swap2(s25);
      var s27 := Dup6(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x353;
      assert s31.Peek(11) == 0x162;
      var s32 := Dup2(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Dup5(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x07fe);
      var s40 := Swap1(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s401(s41, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 148
    * Starting at 0x7f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x7fe

    requires s0.stack[10] == 0x353

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0x7fe;
      assert s1.Peek(10) == 0x353;
      assert s1.Peek(15) == 0x162;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s402(s3, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x7fe

    requires s0.stack[10] == 0x353

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7fe;
      assert s1.Peek(10) == 0x353;
      assert s1.Peek(15) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s405(s9, gas - 1)
      else
        ExecuteFromCFGNode_s403(s9, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x7fe

    requires s0.stack[11] == 0x353

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0x7fe;
      assert s1.Peek(12) == 0x353;
      assert s1.Peek(17) == 0x162;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s3, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0x7fe

    requires s0.stack[12] == 0x353

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0x7fe;
      assert s1.Peek(12) == 0x353;
      assert s1.Peek(17) == 0x162;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0x7fe;
      assert s11.Peek(14) == 0x353;
      assert s11.Peek(19) == 0x162;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 405
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x7fe

    requires s0.stack[11] == 0x353

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7fe;
      assert s1.Peek(11) == 0x353;
      assert s1.Peek(16) == 0x162;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s5, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 149
    * Starting at 0x7fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0x353;
      assert s11.Peek(12) == 0x162;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0x353;
      assert s21.Peek(12) == 0x162;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x0848);
      var s28 := Swap2(s27);
      var s29 := Swap1(s28);
      var s30 := Push2(s29, 0x0f5e);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s31, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 232
    * Starting at 0xf5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x848

    requires s0.stack[10] == 0x353

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x848;
      assert s1.Peek(10) == 0x353;
      assert s1.Peek(15) == 0x162;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s8, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 150
    * Starting at 0x848
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x848 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x085b);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(2) == 0x85b;
      assert s11.Peek(7) == 0x353;
      assert s11.Peek(12) == 0x162;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x094e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s409(s14, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 160
    * Starting at 0x94e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x85b

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x85b;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s5, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 151
    * Starting at 0x85b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x353

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x353;
      assert s1.Peek(9) == 0x162;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s6, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 82
    * Starting at 0x353
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x353 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup5(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x162;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x02);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Dup2(s16);
      var s18 := Keccak256(s17);
      var s19 := Dup2(s18);
      var s20 := Push2(s19, 0x0374);
      var s21 := Push2(s20, 0x067f);
      assert s21.Peek(0) == 0x67f;
      assert s21.Peek(1) == 0x374;
      assert s21.Peek(9) == 0x162;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s22, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x374

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x374;
      assert s1.Peek(8) == 0x162;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s4, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 83
    * Starting at 0x374
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(10) == 0x162;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(7) == 0x162;
      var s22 := Add(s21);
      var s23 := Push1(s22, 0x00);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Swap1(s25);
      var s27 := Pop(s26);
      var s28 := Dup3(s27);
      var s29 := Dup2(s28);
      var s30 := Lt(s29);
      var s31 := IsZero(s30);
      assert s31.Peek(6) == 0x162;
      var s32 := Push2(s31, 0x03c0);
      var s33 := JumpI(s32);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s32.stack[1] > 0 then
        ExecuteFromCFGNode_s417(s33, gas - 1)
      else
        ExecuteFromCFGNode_s414(s33, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 84
    * Starting at 0x3a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(7) == 0x162;
      var s12 := Push2(s11, 0x0da2);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s13, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 225
    * Starting at 0xda2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x3b7

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(7) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x28);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732061);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(8) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push8(s15, 0x6c6c6f77616e6365);
      var s17 := Push1(s16, 0xc0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(9) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s26, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x162;
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

  /** Node 417
    * Segment Id for this node is: 86
    * Starting at 0x3c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x162;
      var s2 := Push2(s1, 0x03d4);
      var s3 := Dup6(s2);
      var s4 := Push2(s3, 0x03cc);
      var s5 := Push2(s4, 0x067f);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s6, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x3cc

    requires s0.stack[2] == 0x3d4

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3cc;
      assert s1.Peek(2) == 0x3d4;
      assert s1.Peek(8) == 0x162;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s419(s4, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 87
    * Starting at 0x3cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3d4

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3d4;
      assert s1.Peek(8) == 0x162;
      var s2 := Dup6(s1);
      var s3 := Dup5(s2);
      var s4 := Sub(s3);
      var s5 := Push2(s4, 0x0683);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s6, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 133
    * Starting at 0x683
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3d4

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d4;
      assert s1.Peek(9) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06a9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s424(s10, gas - 1)
      else
        ExecuteFromCFGNode_s421(s10, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 134
    * Starting at 0x692
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x692 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3d4

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3d4;
      assert s1.Peek(10) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x3d4;
      assert s11.Peek(11) == 0x162;
      var s12 := Push2(s11, 0x0ed5);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s422(s13, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 230
    * Starting at 0xed5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x3d4

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x3d4;
      assert s1.Peek(11) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x24);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x3d4;
      assert s11.Peek(12) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push4(s15, 0x72657373);
      var s17 := Push1(s16, 0xe0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x3d4;
      assert s21.Peek(13) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s26, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 85
    * Starting at 0x3b7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3d4

    requires s0.stack[10] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3d4;
      assert s1.Peek(10) == 0x162;
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

  /** Node 424
    * Segment Id for this node is: 135
    * Starting at 0x6a9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3d4

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d4;
      assert s1.Peek(9) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06cf);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s427(s10, gas - 1)
      else
        ExecuteFromCFGNode_s425(s10, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 136
    * Starting at 0x6b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3d4

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3d4;
      assert s1.Peek(10) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x3d4;
      assert s11.Peek(11) == 0x162;
      var s12 := Push2(s11, 0x0cfa);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s426(s13, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 222
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x3d4

    requires s0.stack[11] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x3d4;
      assert s1.Peek(11) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x3d4;
      assert s11.Peek(12) == 0x162;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x7373);
      var s17 := Push1(s16, 0xf0);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x3b7;
      assert s21.Peek(7) == 0x3d4;
      assert s21.Peek(13) == 0x162;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s26, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 137
    * Starting at 0x6cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3d4

    requires s0.stack[9] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d4;
      assert s1.Peek(9) == 0x162;
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
      assert s11.Peek(7) == 0x3d4;
      assert s11.Peek(13) == 0x162;
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
      assert s21.Peek(10) == 0x3d4;
      assert s21.Peek(16) == 0x162;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Dup8(s23);
      var s25 := And(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := MStore(s27);
      var s29 := Swap5(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(9) == 0x3d4;
      assert s31.Peek(15) == 0x162;
      var s32 := MStore(s31);
      var s33 := Swap1(s32);
      var s34 := Dup2(s33);
      var s35 := Swap1(s34);
      var s36 := Keccak256(s35);
      var s37 := Dup5(s36);
      var s38 := Swap1(s37);
      var s39 := SStore(s38);
      var s40 := MLoad(s39);
      var s41 := Push32(s40, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s428(s41, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 138
    * Starting at 0x71f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x3d4

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(7) == 0x3d4;
      assert s1.Peek(13) == 0x162;
      var s2 := Push2(s1, 0x072a);
      var s3 := Swap1(s2);
      var s4 := Dup6(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0f5e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s429(s7, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 232
    * Starting at 0xf5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x72a

    requires s0.stack[9] == 0x3d4

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x72a;
      assert s1.Peek(9) == 0x3d4;
      assert s1.Peek(15) == 0x162;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s8, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 139
    * Starting at 0x72a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x3d4

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3d4;
      assert s1.Peek(13) == 0x162;
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
      assert s11.Peek(0) == 0x3d4;
      assert s11.Peek(6) == 0x162;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s431(s12, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 88
    * Starting at 0x3d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x162;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap5(s3);
      var s5 := Swap4(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s10, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 170
    * Starting at 0xa12
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x353

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a2b);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s434(s9, gas - 1)
      else
        ExecuteFromCFGNode_s433(s9, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 171
    * Starting at 0xa1f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := And(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s434(s8, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 172
    * Starting at 0xa2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x094e);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s395(s4, gas - 1)
      else
        ExecuteFromCFGNode_s435(s4, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 173
    * Starting at 0xa31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x353

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x07);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0a3d);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x04b4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s7, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 102
    * Starting at 0x4b4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xa3d

    requires s0.stack[7] == 0x78e

    requires s0.stack[11] == 0x353

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa3d;
      assert s1.Peek(7) == 0x78e;
      assert s1.Peek(11) == 0x353;
      assert s1.Peek(16) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0xa3d;
      assert s11.Peek(10) == 0x78e;
      assert s11.Peek(14) == 0x353;
      assert s11.Peek(19) == 0x162;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s437(s19, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xa3d

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x353

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa3d;
      assert s1.Peek(8) == 0x78e;
      assert s1.Peek(12) == 0x353;
      assert s1.Peek(17) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s438(s5, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 174
    * Starting at 0xa3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x78e

    requires s0.stack[10] == 0x353

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x78e;
      assert s1.Peek(10) == 0x353;
      assert s1.Peek(15) == 0x162;
      var s2 := Push2(s1, 0x0a47);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0f75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s6, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xa47

    requires s0.stack[7] == 0x78e

    requires s0.stack[11] == 0x353

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa47;
      assert s1.Peek(7) == 0x78e;
      assert s1.Peek(11) == 0x353;
      assert s1.Peek(16) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s442(s9, gas - 1)
      else
        ExecuteFromCFGNode_s440(s9, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xa47

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x353

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa47;
      assert s1.Peek(9) == 0x78e;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(18) == 0x162;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s441(s3, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0xa47

    requires s0.stack[9] == 0x78e

    requires s0.stack[13] == 0x353

    requires s0.stack[18] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa47;
      assert s1.Peek(9) == 0x78e;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(18) == 0x162;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0xa47;
      assert s11.Peek(11) == 0x78e;
      assert s11.Peek(15) == 0x353;
      assert s11.Peek(20) == 0x162;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 442
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xa47

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x353

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa47;
      assert s1.Peek(8) == 0x78e;
      assert s1.Peek(12) == 0x353;
      assert s1.Peek(17) == 0x162;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s5, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 175
    * Starting at 0xa47
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa47 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x78e

    requires s0.stack[9] == 0x353

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x78e;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(14) == 0x162;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a6a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s453(s7, gas - 1)
      else
        ExecuteFromCFGNode_s444(s7, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 176
    * Starting at 0xa50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x78e;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(12) == 0x162;
      var s2 := Push1(s1, 0x08);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x0a5d);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x04b4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s8, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 102
    * Starting at 0x4b4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xa5d

    requires s0.stack[7] == 0x78e

    requires s0.stack[11] == 0x353

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa5d;
      assert s1.Peek(7) == 0x78e;
      assert s1.Peek(11) == 0x353;
      assert s1.Peek(16) == 0x162;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0xa5d;
      assert s11.Peek(10) == 0x78e;
      assert s11.Peek(14) == 0x353;
      assert s11.Peek(19) == 0x162;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s446(s19, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xa5d

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x353

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa5d;
      assert s1.Peek(8) == 0x78e;
      assert s1.Peek(12) == 0x353;
      assert s1.Peek(17) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s447(s5, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 177
    * Starting at 0xa5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x78e

    requires s0.stack[10] == 0x353

    requires s0.stack[15] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x78e;
      assert s1.Peek(10) == 0x353;
      assert s1.Peek(15) == 0x162;
      var s2 := Push2(s1, 0x0a67);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0f75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s6, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 234
    * Starting at 0xf75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xa67

    requires s0.stack[7] == 0x78e

    requires s0.stack[11] == 0x353

    requires s0.stack[16] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa67;
      assert s1.Peek(7) == 0x78e;
      assert s1.Peek(11) == 0x353;
      assert s1.Peek(16) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0f88);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s451(s9, gas - 1)
      else
        ExecuteFromCFGNode_s449(s9, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 235
    * Starting at 0xf81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xa67

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x353

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f88);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa67;
      assert s1.Peek(9) == 0x78e;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(18) == 0x162;
      var s2 := Push2(s1, 0x0fdf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s3, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 245
    * Starting at 0xfdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xf88

    requires s0.stack[4] == 0xa67

    requires s0.stack[9] == 0x78e

    requires s0.stack[13] == 0x353

    requires s0.stack[18] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf88;
      assert s1.Peek(4) == 0xa67;
      assert s1.Peek(9) == 0x78e;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(18) == 0x162;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xf88;
      assert s11.Peek(6) == 0xa67;
      assert s11.Peek(11) == 0x78e;
      assert s11.Peek(15) == 0x353;
      assert s11.Peek(20) == 0x162;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 451
    * Segment Id for this node is: 236
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xa67

    requires s0.stack[8] == 0x78e

    requires s0.stack[12] == 0x353

    requires s0.stack[17] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa67;
      assert s1.Peek(8) == 0x78e;
      assert s1.Peek(12) == 0x353;
      assert s1.Peek(17) == 0x162;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s5, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 178
    * Starting at 0xa67
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x78e

    requires s0.stack[9] == 0x353

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x78e;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(14) == 0x162;
      var s2 := Lt(s1);
      var s3 := IsZero(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s453(s3, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 179
    * Starting at 0xa6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x78e

    requires s0.stack[8] == 0x353

    requires s0.stack[13] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := Push2(s1, 0x094e);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s395(s3, gas - 1)
      else
        ExecuteFromCFGNode_s454(s3, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 180
    * Starting at 0xa6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x78e

    requires s0.stack[7] == 0x353

    requires s0.stack[12] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x78e;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(13) == 0x162;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03b7);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3b7;
      assert s11.Peek(5) == 0x78e;
      assert s11.Peek(9) == 0x353;
      assert s11.Peek(14) == 0x162;
      var s12 := Push2(s11, 0x0d82);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s455(s13, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 224
    * Starting at 0xd82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x3b7

    requires s0.stack[5] == 0x78e

    requires s0.stack[9] == 0x353

    requires s0.stack[14] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b7;
      assert s1.Peek(5) == 0x78e;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(14) == 0x162;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x06);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 6, 0x119bdc989a59);
      assert s11.Peek(2) == 0x3b7;
      assert s11.Peek(6) == 0x78e;
      assert s11.Peek(10) == 0x353;
      assert s11.Peek(15) == 0x162;
      var s12 := Push1(s11, 0xd2);
      var s13 := Shl(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s21, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 38
    * Starting at 0x184
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x184 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0177);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s457(s4, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 80
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x177;
      var s2 := Push1(s1, 0x08);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s5, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 36
    * Starting at 0x16f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0177);
      var s3 := Push2(s2, 0x033a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s4, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 79
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x177

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x177;
      var s2 := Push1(s1, 0x03);
      var s3 := SLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s5, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 33
    * Starting at 0x14f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0162);
      var s3 := Push2(s2, 0x015d);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0b3b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s7, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 199
    * Starting at 0xb3b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x15d

    requires s0.stack[3] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15d;
      assert s1.Peek(3) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0b4d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s463(s11, gas - 1)
      else
        ExecuteFromCFGNode_s462(s11, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 200
    * Starting at 0xb4a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x15d

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x15d;
      assert s1.Peek(6) == 0x162;
      var s2 := Dup3(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 463
    * Segment Id for this node is: 201
    * Starting at 0xb4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x15d

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x15d;
      assert s1.Peek(5) == 0x162;
      var s2 := Push2(s1, 0x0b56);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s5, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 181
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb56

    requires s0.stack[6] == 0x15d

    requires s0.stack[7] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb56;
      assert s1.Peek(6) == 0x15d;
      assert s1.Peek(7) == 0x162;
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
      assert s11.Peek(4) == 0xb56;
      assert s11.Peek(9) == 0x15d;
      assert s11.Peek(10) == 0x162;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x04ce);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s466(s14, gas - 1)
      else
        ExecuteFromCFGNode_s465(s14, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 182
    * Starting at 0xa99
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb56

    requires s0.stack[7] == 0x15d

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xb56;
      assert s1.Peek(8) == 0x15d;
      assert s1.Peek(9) == 0x162;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 466
    * Segment Id for this node is: 103
    * Starting at 0x4ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb56

    requires s0.stack[7] == 0x15d

    requires s0.stack[8] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb56;
      assert s1.Peek(7) == 0x15d;
      assert s1.Peek(8) == 0x162;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s467(s5, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 202
    * Starting at 0xb56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x15d

    requires s0.stack[6] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x15d;
      assert s1.Peek(6) == 0x162;
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
      assert s11.Peek(1) == 0x15d;
      assert s11.Peek(4) == 0x162;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s468(s13, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 34
    * Starting at 0x15d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      var s2 := Push2(s1, 0x031d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s3, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 76
    * Starting at 0x31d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0331);
      var s4 := Push2(s3, 0x032a);
      var s5 := Push2(s4, 0x067f);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s470(s6, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 132
    * Starting at 0x67f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x32a

    requires s0.stack[1] == 0x331

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x32a;
      assert s1.Peek(1) == 0x331;
      assert s1.Peek(5) == 0x162;
      var s2 := Caller(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s4, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 77
    * Starting at 0x32a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x331

    requires s0.stack[5] == 0x162

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x331;
      assert s1.Peek(5) == 0x162;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x0683);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s5, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 30
    * Starting at 0x131
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0139);
      var s3 := Push2(s2, 0x028b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s4, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 67
    * Starting at 0x28b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x029a);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0fa4);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s9, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 29
    * Starting at 0x12c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c as nat
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
