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
        ExecuteFromCFGNode_s751(s7, gas - 1)
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
      var s6 := Push4(s5, 0x70a08231);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0097);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s343(s9, gas - 1)
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
      var s2 := Push4(s1, 0xa457c2d7);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0066);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s242(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa457c2d7);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0276);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02a6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02d6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0306);
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
      var s1 := Push2(s0, 0x00f5);
      assert s1.Peek(0) == 0xf5;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 24
    * Starting at 0xf5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
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

  /** Node 11
    * Segment Id for this node is: 73
    * Starting at 0x306
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x306 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0320);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x031b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x31b;
      assert s11.Peek(3) == 0x320;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0ec9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s14, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 189
    * Starting at 0xec9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x31b

    requires s0.stack[3] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31b;
      assert s1.Peek(3) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0edb);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s10, gas - 1)
      else
        ExecuteFromCFGNode_s13(s10, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 190
    * Starting at 0xed7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x31b

    requires s0.stack[4] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x31b;
      assert s1.Peek(5) == 0x320;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 14
    * Segment Id for this node is: 191
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x31b

    requires s0.stack[4] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x31b;
      assert s1.Peek(4) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ee9);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s9, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xee9

    requires s0.stack[7] == 0x31b

    requires s0.stack[8] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xee9;
      assert s1.Peek(7) == 0x31b;
      assert s1.Peek(8) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s10, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xee9

    requires s0.stack[10] == 0x31b

    requires s0.stack[11] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xee9;
      assert s1.Peek(10) == 0x31b;
      assert s1.Peek(11) == 0x320;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xee9

    requires s0.stack[12] == 0x31b

    requires s0.stack[13] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xee9;
      assert s1.Peek(12) == 0x31b;
      assert s1.Peek(13) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s6, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xee9

    requires s0.stack[15] == 0x31b

    requires s0.stack[16] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xee9;
      assert s1.Peek(15) == 0x31b;
      assert s1.Peek(16) == 0x320;
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
      ExecuteFromCFGNode_s19(s11, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xee9

    requires s0.stack[14] == 0x31b

    requires s0.stack[15] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xee9;
      assert s1.Peek(14) == 0x31b;
      assert s1.Peek(15) == 0x320;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s7, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xee9

    requires s0.stack[11] == 0x31b

    requires s0.stack[12] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xee9;
      assert s1.Peek(11) == 0x31b;
      assert s1.Peek(12) == 0x320;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s5, gas - 1)
      else
        ExecuteFromCFGNode_s21(s5, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xee9

    requires s0.stack[10] == 0x31b

    requires s0.stack[11] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xee9;
      assert s1.Peek(11) == 0x31b;
      assert s1.Peek(12) == 0x320;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 22
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xee9

    requires s0.stack[10] == 0x31b

    requires s0.stack[11] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xee9;
      assert s1.Peek(10) == 0x31b;
      assert s1.Peek(11) == 0x320;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s3, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xee9

    requires s0.stack[8] == 0x31b

    requires s0.stack[9] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee9;
      assert s1.Peek(8) == 0x31b;
      assert s1.Peek(9) == 0x320;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s6, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 192
    * Starting at 0xee9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x31b

    requires s0.stack[6] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x31b;
      assert s1.Peek(6) == 0x320;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s9, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 74
    * Starting at 0x31b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x320;
      var s2 := Push2(s1, 0x069f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s3, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 128
    * Starting at 0x69f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x320;
      var s2 := Push2(s1, 0x06a7);
      var s3 := Push2(s2, 0x0bfa);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s4, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 166
    * Starting at 0xbfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x6a7

    requires s0.stack[2] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6a7;
      assert s1.Peek(2) == 0x320;
      var s2 := Push2(s1, 0x0c02);
      var s3 := Push2(s2, 0x0723);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s4, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 134
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0xc02

    requires s0.stack[1] == 0x6a7

    requires s0.stack[3] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc02;
      assert s1.Peek(1) == 0x6a7;
      assert s1.Peek(3) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s7, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 167
    * Starting at 0xc02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x6a7

    requires s0.stack[3] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6a7;
      assert s1.Peek(3) == 0x320;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0c20);
      var s5 := Push2(s4, 0x04c2);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 106
    * Starting at 0x4c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0xc20

    requires s0.stack[2] == 0x6a7

    requires s0.stack[4] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc20;
      assert s1.Peek(2) == 0x6a7;
      assert s1.Peek(4) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0xc20;
      assert s11.Peek(4) == 0x6a7;
      assert s11.Peek(6) == 0x320;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s17, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 168
    * Starting at 0xc20
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x6a7

    requires s0.stack[4] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6a7;
      assert s1.Peek(4) == 0x320;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0c76);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s6, gas - 1)
      else
        ExecuteFromCFGNode_s32(s6, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 169
    * Starting at 0xc3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x6a7

    requires s0.stack[2] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x6a7;
      assert s1.Peek(3) == 0x320;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c6d);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1284);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s11, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 268
    * Starting at 0x1284
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1284 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0xc6d

    requires s0.stack[2] == 0x6a7

    requires s0.stack[4] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6d;
      assert s1.Peek(2) == 0x6a7;
      assert s1.Peek(4) == 0x320;
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
      assert s11.Peek(4) == 0xc6d;
      assert s11.Peek(5) == 0x6a7;
      assert s11.Peek(7) == 0x320;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x129d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10bf);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s18, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 233
    * Starting at 0x10bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x129d

    requires s0.stack[4] == 0xc6d

    requires s0.stack[5] == 0x6a7

    requires s0.stack[7] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x129d;
      assert s1.Peek(4) == 0xc6d;
      assert s1.Peek(5) == 0x6a7;
      assert s1.Peek(7) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10cc);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s7, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x10cc

    requires s0.stack[5] == 0x129d

    requires s0.stack[8] == 0xc6d

    requires s0.stack[9] == 0x6a7

    requires s0.stack[11] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10cc;
      assert s1.Peek(5) == 0x129d;
      assert s1.Peek(8) == 0xc6d;
      assert s1.Peek(9) == 0x6a7;
      assert s1.Peek(11) == 0x320;
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
      assert s11.Peek(0) == 0x10cc;
      assert s11.Peek(6) == 0x129d;
      assert s11.Peek(9) == 0xc6d;
      assert s11.Peek(10) == 0x6a7;
      assert s11.Peek(12) == 0x320;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s15, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 234
    * Starting at 0x10cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x129d

    requires s0.stack[6] == 0xc6d

    requires s0.stack[7] == 0x6a7

    requires s0.stack[9] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x129d;
      assert s1.Peek(6) == 0xc6d;
      assert s1.Peek(7) == 0x6a7;
      assert s1.Peek(9) == 0x320;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10d7);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x165a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s7, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 316
    * Starting at 0x165a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x165a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x10d7

    requires s0.stack[4] == 0x129d

    requires s0.stack[7] == 0xc6d

    requires s0.stack[8] == 0x6a7

    requires s0.stack[10] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d7;
      assert s1.Peek(4) == 0x129d;
      assert s1.Peek(7) == 0xc6d;
      assert s1.Peek(8) == 0x6a7;
      assert s1.Peek(10) == 0x320;
      var s2 := Push32(s1, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s8, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 235
    * Starting at 0x10d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x129d

    requires s0.stack[5] == 0xc6d

    requires s0.stack[6] == 0x6a7

    requires s0.stack[8] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x129d;
      assert s1.Peek(5) == 0xc6d;
      assert s1.Peek(6) == 0x6a7;
      assert s1.Peek(8) == 0x320;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s10, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 269
    * Starting at 0x129d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xc6d

    requires s0.stack[4] == 0x6a7

    requires s0.stack[6] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc6d;
      assert s1.Peek(4) == 0x6a7;
      assert s1.Peek(6) == 0x320;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s7, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 170
    * Starting at 0xc6d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x6a7

    requires s0.stack[3] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6a7;
      assert s1.Peek(3) == 0x320;
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

  /** Node 41
    * Segment Id for this node is: 171
    * Starting at 0xc76
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x6a7

    requires s0.stack[2] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6a7;
      assert s1.Peek(2) == 0x320;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s2, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 129
    * Starting at 0x6a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0717);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s11, gas - 1)
      else
        ExecuteFromCFGNode_s43(s11, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 130
    * Starting at 0x6dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x320;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x070e);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1204);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s11, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 260
    * Starting at 0x1204
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1204 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x70e

    requires s0.stack[3] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x70e;
      assert s1.Peek(3) == 0x320;
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
      assert s11.Peek(4) == 0x70e;
      assert s11.Peek(6) == 0x320;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x121d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1033);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s18, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 221
    * Starting at 0x1033
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1033 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x121d

    requires s0.stack[4] == 0x70e

    requires s0.stack[6] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x121d;
      assert s1.Peek(4) == 0x70e;
      assert s1.Peek(6) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1040);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s7, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1040

    requires s0.stack[5] == 0x121d

    requires s0.stack[8] == 0x70e

    requires s0.stack[10] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1040;
      assert s1.Peek(5) == 0x121d;
      assert s1.Peek(8) == 0x70e;
      assert s1.Peek(10) == 0x320;
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
      assert s11.Peek(0) == 0x1040;
      assert s11.Peek(6) == 0x121d;
      assert s11.Peek(9) == 0x70e;
      assert s11.Peek(11) == 0x320;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s15, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 222
    * Starting at 0x1040
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1040 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x121d

    requires s0.stack[6] == 0x70e

    requires s0.stack[8] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x121d;
      assert s1.Peek(6) == 0x70e;
      assert s1.Peek(8) == 0x320;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x104b);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1544);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s7, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 312
    * Starting at 0x1544
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1544 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x104b

    requires s0.stack[4] == 0x121d

    requires s0.stack[7] == 0x70e

    requires s0.stack[9] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x104b;
      assert s1.Peek(4) == 0x121d;
      assert s1.Peek(7) == 0x70e;
      assert s1.Peek(9) == 0x320;
      var s2 := Push32(s1, 0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6464726573730000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x104b;
      assert s11.Peek(4) == 0x121d;
      assert s11.Peek(7) == 0x70e;
      assert s11.Peek(9) == 0x320;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s13, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 223
    * Starting at 0x104b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x121d

    requires s0.stack[5] == 0x70e

    requires s0.stack[7] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x121d;
      assert s1.Peek(5) == 0x70e;
      assert s1.Peek(7) == 0x320;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s10, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 261
    * Starting at 0x121d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x70e

    requires s0.stack[5] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x70e;
      assert s1.Peek(5) == 0x320;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s7, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 131
    * Starting at 0x70e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x320;
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

  /** Node 52
    * Segment Id for this node is: 132
    * Starting at 0x717
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x717 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x320;
      var s2 := Push2(s1, 0x0720);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dcf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s5, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 181
    * Starting at 0xdcf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x720

    requires s0.stack[3] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x720;
      assert s1.Peek(3) == 0x320;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x720;
      assert s11.Peek(5) == 0x320;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x05);
      var s18 := Push1(s17, 0x00);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x720;
      assert s21.Peek(8) == 0x320;
      var s22 := SLoad(s21);
      var s23 := Dup2(s22);
      var s24 := Push20(s23, 0xffffffffffffffffffffffffffffffffffffffff);
      var s25 := Mul(s24);
      var s26 := Not(s25);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Dup4(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(7) == 0x720;
      assert s31.Peek(9) == 0x320;
      var s32 := Mul(s31);
      var s33 := Or(s32);
      var s34 := Swap1(s33);
      var s35 := SStore(s34);
      var s36 := Pop(s35);
      var s37 := Dup2(s36);
      var s38 := Push20(s37, 0xffffffffffffffffffffffffffffffffffffffff);
      var s39 := And(s38);
      var s40 := Dup2(s39);
      var s41 := Push20(s40, 0xffffffffffffffffffffffffffffffffffffffff);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s54(s41, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 182
    * Starting at 0xe65
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x720

    requires s0.stack[7] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x720;
      assert s1.Peek(6) == 0x320;
      var s2 := Push32(s1, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Swap2(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Log3(s10);
      assert s11.Peek(2) == 0x720;
      assert s11.Peek(4) == 0x320;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s14, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 133
    * Starting at 0x720
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x720 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x320

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x320;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s3, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 75
    * Starting at 0x320
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x320 as nat
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

  /** Node 57
    * Segment Id for this node is: 69
    * Starting at 0x2d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x02f0);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x02eb);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x2eb;
      assert s11.Peek(3) == 0x2f0;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0ef2);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s14, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 193
    * Starting at 0xef2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2eb

    requires s0.stack[3] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2eb;
      assert s1.Peek(3) == 0x2f0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f05);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s11, gas - 1)
      else
        ExecuteFromCFGNode_s59(s11, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 194
    * Starting at 0xf01
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2eb

    requires s0.stack[5] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x2eb;
      assert s1.Peek(6) == 0x2f0;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 60
    * Segment Id for this node is: 195
    * Starting at 0xf05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2eb

    requires s0.stack[5] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2eb;
      assert s1.Peek(5) == 0x2f0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f13);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s9, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf13

    requires s0.stack[8] == 0x2eb

    requires s0.stack[9] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf13;
      assert s1.Peek(8) == 0x2eb;
      assert s1.Peek(9) == 0x2f0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s10, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf13

    requires s0.stack[11] == 0x2eb

    requires s0.stack[12] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf13;
      assert s1.Peek(11) == 0x2eb;
      assert s1.Peek(12) == 0x2f0;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s5, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf13

    requires s0.stack[13] == 0x2eb

    requires s0.stack[14] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf13;
      assert s1.Peek(13) == 0x2eb;
      assert s1.Peek(14) == 0x2f0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s6, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf13

    requires s0.stack[16] == 0x2eb

    requires s0.stack[17] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf13;
      assert s1.Peek(16) == 0x2eb;
      assert s1.Peek(17) == 0x2f0;
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
      ExecuteFromCFGNode_s65(s11, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf13

    requires s0.stack[15] == 0x2eb

    requires s0.stack[16] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf13;
      assert s1.Peek(15) == 0x2eb;
      assert s1.Peek(16) == 0x2f0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s7, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf13

    requires s0.stack[12] == 0x2eb

    requires s0.stack[13] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf13;
      assert s1.Peek(12) == 0x2eb;
      assert s1.Peek(13) == 0x2f0;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s5, gas - 1)
      else
        ExecuteFromCFGNode_s67(s5, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf13

    requires s0.stack[11] == 0x2eb

    requires s0.stack[12] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf13;
      assert s1.Peek(12) == 0x2eb;
      assert s1.Peek(13) == 0x2f0;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 68
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf13

    requires s0.stack[11] == 0x2eb

    requires s0.stack[12] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf13;
      assert s1.Peek(11) == 0x2eb;
      assert s1.Peek(12) == 0x2f0;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s3, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf13

    requires s0.stack[9] == 0x2eb

    requires s0.stack[10] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf13;
      assert s1.Peek(9) == 0x2eb;
      assert s1.Peek(10) == 0x2f0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s6, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 196
    * Starting at 0xf13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x2eb

    requires s0.stack[7] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2eb;
      assert s1.Peek(7) == 0x2f0;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0f24);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0e9f);
      assert s11.Peek(0) == 0xe9f;
      assert s11.Peek(3) == 0xf24;
      assert s11.Peek(9) == 0x2eb;
      assert s11.Peek(10) == 0x2f0;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s12, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf24

    requires s0.stack[8] == 0x2eb

    requires s0.stack[9] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf24;
      assert s1.Peek(8) == 0x2eb;
      assert s1.Peek(9) == 0x2f0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s10, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf24

    requires s0.stack[11] == 0x2eb

    requires s0.stack[12] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf24;
      assert s1.Peek(11) == 0x2eb;
      assert s1.Peek(12) == 0x2f0;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s5, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf24

    requires s0.stack[13] == 0x2eb

    requires s0.stack[14] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf24;
      assert s1.Peek(13) == 0x2eb;
      assert s1.Peek(14) == 0x2f0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s6, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf24

    requires s0.stack[16] == 0x2eb

    requires s0.stack[17] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf24;
      assert s1.Peek(16) == 0x2eb;
      assert s1.Peek(17) == 0x2f0;
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
      ExecuteFromCFGNode_s75(s11, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf24

    requires s0.stack[15] == 0x2eb

    requires s0.stack[16] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf24;
      assert s1.Peek(15) == 0x2eb;
      assert s1.Peek(16) == 0x2f0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s7, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf24

    requires s0.stack[12] == 0x2eb

    requires s0.stack[13] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf24;
      assert s1.Peek(12) == 0x2eb;
      assert s1.Peek(13) == 0x2f0;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s5, gas - 1)
      else
        ExecuteFromCFGNode_s77(s5, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf24

    requires s0.stack[11] == 0x2eb

    requires s0.stack[12] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf24;
      assert s1.Peek(12) == 0x2eb;
      assert s1.Peek(13) == 0x2f0;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 78
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf24

    requires s0.stack[11] == 0x2eb

    requires s0.stack[12] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf24;
      assert s1.Peek(11) == 0x2eb;
      assert s1.Peek(12) == 0x2f0;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s3, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf24

    requires s0.stack[9] == 0x2eb

    requires s0.stack[10] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf24;
      assert s1.Peek(9) == 0x2eb;
      assert s1.Peek(10) == 0x2f0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s6, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 197
    * Starting at 0xf24
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x2eb

    requires s0.stack[7] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2eb;
      assert s1.Peek(7) == 0x2f0;
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
      ExecuteFromCFGNode_s81(s10, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 70
    * Starting at 0x2eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2f0;
      var s2 := Push2(s1, 0x0618);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s3, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 126
    * Starting at 0x618
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x618 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2f0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x2f0;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x2f0;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x2f0;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s83(s41, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 127
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x2f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x2f0;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s4, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 71
    * Starting at 0x2f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x02fd);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1324);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s8, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fd;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0x2fd;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s14, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0x2fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0x2fd;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s5, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0x2fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0x2fd;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s9, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0x2fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0x2fd;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s6, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x2fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fd;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s6, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 72
    * Starting at 0x2fd
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fd as nat
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

  /** Node 91
    * Segment Id for this node is: 65
    * Starting at 0x2a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x02c0);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x02bb);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x2bb;
      assert s11.Peek(3) == 0x2c0;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f7d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s14, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 204
    * Starting at 0xf7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2bb

    requires s0.stack[3] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2bb;
      assert s1.Peek(3) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f90);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s11, gas - 1)
      else
        ExecuteFromCFGNode_s93(s11, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 205
    * Starting at 0xf8c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2bb

    requires s0.stack[5] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x2bb;
      assert s1.Peek(6) == 0x2c0;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 94
    * Segment Id for this node is: 206
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2bb

    requires s0.stack[5] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2bb;
      assert s1.Peek(5) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f9e);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s9, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf9e

    requires s0.stack[8] == 0x2bb

    requires s0.stack[9] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9e;
      assert s1.Peek(8) == 0x2bb;
      assert s1.Peek(9) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s10, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x2bb

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x2bb;
      assert s1.Peek(12) == 0x2c0;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s5, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf9e

    requires s0.stack[13] == 0x2bb

    requires s0.stack[14] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf9e;
      assert s1.Peek(13) == 0x2bb;
      assert s1.Peek(14) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s6, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf9e

    requires s0.stack[16] == 0x2bb

    requires s0.stack[17] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf9e;
      assert s1.Peek(16) == 0x2bb;
      assert s1.Peek(17) == 0x2c0;
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
      ExecuteFromCFGNode_s99(s11, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf9e

    requires s0.stack[15] == 0x2bb

    requires s0.stack[16] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf9e;
      assert s1.Peek(15) == 0x2bb;
      assert s1.Peek(16) == 0x2c0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s7, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf9e

    requires s0.stack[12] == 0x2bb

    requires s0.stack[13] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x2bb;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s5, gas - 1)
      else
        ExecuteFromCFGNode_s101(s5, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x2bb

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x2bb;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 102
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x2bb

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x2bb;
      assert s1.Peek(12) == 0x2c0;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s3, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf9e

    requires s0.stack[9] == 0x2bb

    requires s0.stack[10] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9e;
      assert s1.Peek(9) == 0x2bb;
      assert s1.Peek(10) == 0x2c0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 207
    * Starting at 0xf9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x2bb

    requires s0.stack[7] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2bb;
      assert s1.Peek(7) == 0x2c0;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0faf);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0eb4);
      assert s11.Peek(0) == 0xeb4;
      assert s11.Peek(3) == 0xfaf;
      assert s11.Peek(9) == 0x2bb;
      assert s11.Peek(10) == 0x2c0;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s12, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 187
    * Starting at 0xeb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xfaf

    requires s0.stack[8] == 0x2bb

    requires s0.stack[9] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaf;
      assert s1.Peek(8) == 0x2bb;
      assert s1.Peek(9) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ec3);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x17b0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s10, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 325
    * Starting at 0x17b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x2bb

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x2bb;
      assert s1.Peek(12) == 0x2c0;
      var s2 := Push2(s1, 0x17b9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s5, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17b9

    requires s0.stack[3] == 0xec3

    requires s0.stack[7] == 0xfaf

    requires s0.stack[13] == 0x2bb

    requires s0.stack[14] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17b9;
      assert s1.Peek(3) == 0xec3;
      assert s1.Peek(7) == 0xfaf;
      assert s1.Peek(13) == 0x2bb;
      assert s1.Peek(14) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s9, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 326
    * Starting at 0x17b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xec3

    requires s0.stack[6] == 0xfaf

    requires s0.stack[12] == 0x2bb

    requires s0.stack[13] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x2bb;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17c4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s5, gas - 1)
      else
        ExecuteFromCFGNode_s109(s5, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 327
    * Starting at 0x17c0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x2bb

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x2bb;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 110
    * Segment Id for this node is: 328
    * Starting at 0x17c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x2bb

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x2bb;
      assert s1.Peek(12) == 0x2c0;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s3, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 188
    * Starting at 0xec3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xfaf

    requires s0.stack[9] == 0x2bb

    requires s0.stack[10] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfaf;
      assert s1.Peek(9) == 0x2bb;
      assert s1.Peek(10) == 0x2c0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s6, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 208
    * Starting at 0xfaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x2bb

    requires s0.stack[7] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2bb;
      assert s1.Peek(7) == 0x2c0;
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
      ExecuteFromCFGNode_s113(s10, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 66
    * Starting at 0x2bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2c0;
      var s2 := Push2(s1, 0x05f5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s3, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 123
    * Starting at 0x5f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0600);
      var s5 := Push2(s4, 0x0723);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s6, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 134
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x600

    requires s0.stack[5] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x600;
      assert s1.Peek(5) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s7, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 124
    * Starting at 0x600
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x600 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2c0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x060d);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x0982);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s9, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 152
    * Starting at 0x982
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x982 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x60d

    requires s0.stack[8] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x60d;
      assert s1.Peek(8) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x09f2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s11, gas - 1)
      else
        ExecuteFromCFGNode_s118(s11, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 153
    * Starting at 0x9b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x60d

    requires s0.stack[8] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x60d;
      assert s1.Peek(9) == 0x2c0;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x09e9);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12a4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s11, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 270
    * Starting at 0x12a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x9e9

    requires s0.stack[5] == 0x60d

    requires s0.stack[10] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9e9;
      assert s1.Peek(5) == 0x60d;
      assert s1.Peek(10) == 0x2c0;
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
      assert s11.Peek(4) == 0x9e9;
      assert s11.Peek(8) == 0x60d;
      assert s11.Peek(13) == 0x2c0;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12bd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10e2);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s18, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 236
    * Starting at 0x10e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x12bd

    requires s0.stack[4] == 0x9e9

    requires s0.stack[8] == 0x60d

    requires s0.stack[13] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12bd;
      assert s1.Peek(4) == 0x9e9;
      assert s1.Peek(8) == 0x60d;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10ef);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s7, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x10ef

    requires s0.stack[5] == 0x12bd

    requires s0.stack[8] == 0x9e9

    requires s0.stack[12] == 0x60d

    requires s0.stack[17] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ef;
      assert s1.Peek(5) == 0x12bd;
      assert s1.Peek(8) == 0x9e9;
      assert s1.Peek(12) == 0x60d;
      assert s1.Peek(17) == 0x2c0;
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
      assert s11.Peek(0) == 0x10ef;
      assert s11.Peek(6) == 0x12bd;
      assert s11.Peek(9) == 0x9e9;
      assert s11.Peek(13) == 0x60d;
      assert s11.Peek(18) == 0x2c0;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s15, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 237
    * Starting at 0x10ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x12bd

    requires s0.stack[6] == 0x9e9

    requires s0.stack[10] == 0x60d

    requires s0.stack[15] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12bd;
      assert s1.Peek(6) == 0x9e9;
      assert s1.Peek(10) == 0x60d;
      assert s1.Peek(15) == 0x2c0;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10fa);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1683);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s7, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 317
    * Starting at 0x1683
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x10fa

    requires s0.stack[4] == 0x12bd

    requires s0.stack[7] == 0x9e9

    requires s0.stack[11] == 0x60d

    requires s0.stack[16] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10fa;
      assert s1.Peek(4) == 0x12bd;
      assert s1.Peek(7) == 0x9e9;
      assert s1.Peek(11) == 0x60d;
      assert s1.Peek(16) == 0x2c0;
      var s2 := Push32(s1, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x10fa;
      assert s11.Peek(4) == 0x12bd;
      assert s11.Peek(7) == 0x9e9;
      assert s11.Peek(11) == 0x60d;
      assert s11.Peek(16) == 0x2c0;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s13, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 238
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x12bd

    requires s0.stack[5] == 0x9e9

    requires s0.stack[9] == 0x60d

    requires s0.stack[14] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12bd;
      assert s1.Peek(5) == 0x9e9;
      assert s1.Peek(9) == 0x60d;
      assert s1.Peek(14) == 0x2c0;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s10, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 271
    * Starting at 0x12bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9e9

    requires s0.stack[7] == 0x60d

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9e9;
      assert s1.Peek(7) == 0x60d;
      assert s1.Peek(12) == 0x2c0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s7, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 154
    * Starting at 0x9e9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x60d

    requires s0.stack[9] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60d;
      assert s1.Peek(9) == 0x2c0;
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
    * Segment Id for this node is: 155
    * Starting at 0x9f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x60d

    requires s0.stack[8] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x60d;
      assert s1.Peek(8) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0a62);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s11, gas - 1)
      else
        ExecuteFromCFGNode_s128(s11, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 156
    * Starting at 0xa28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x60d

    requires s0.stack[8] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x60d;
      assert s1.Peek(9) == 0x2c0;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a59);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x11e4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s11, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 258
    * Starting at 0x11e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xa59

    requires s0.stack[5] == 0x60d

    requires s0.stack[10] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa59;
      assert s1.Peek(5) == 0x60d;
      assert s1.Peek(10) == 0x2c0;
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
      assert s11.Peek(4) == 0xa59;
      assert s11.Peek(8) == 0x60d;
      assert s11.Peek(13) == 0x2c0;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x11fd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1010);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s18, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 218
    * Starting at 0x1010
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1010 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x11fd

    requires s0.stack[4] == 0xa59

    requires s0.stack[8] == 0x60d

    requires s0.stack[13] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11fd;
      assert s1.Peek(4) == 0xa59;
      assert s1.Peek(8) == 0x60d;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x101d);
      var s4 := Push1(s3, 0x23);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s7, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x101d

    requires s0.stack[5] == 0x11fd

    requires s0.stack[8] == 0xa59

    requires s0.stack[12] == 0x60d

    requires s0.stack[17] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x101d;
      assert s1.Peek(5) == 0x11fd;
      assert s1.Peek(8) == 0xa59;
      assert s1.Peek(12) == 0x60d;
      assert s1.Peek(17) == 0x2c0;
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
      assert s11.Peek(0) == 0x101d;
      assert s11.Peek(6) == 0x11fd;
      assert s11.Peek(9) == 0xa59;
      assert s11.Peek(13) == 0x60d;
      assert s11.Peek(18) == 0x2c0;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s15, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 219
    * Starting at 0x101d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x11fd

    requires s0.stack[6] == 0xa59

    requires s0.stack[10] == 0x60d

    requires s0.stack[15] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11fd;
      assert s1.Peek(6) == 0xa59;
      assert s1.Peek(10) == 0x60d;
      assert s1.Peek(15) == 0x2c0;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1028);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x14f5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s7, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 311
    * Starting at 0x14f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1028

    requires s0.stack[4] == 0x11fd

    requires s0.stack[7] == 0xa59

    requires s0.stack[11] == 0x60d

    requires s0.stack[16] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1028;
      assert s1.Peek(4) == 0x11fd;
      assert s1.Peek(7) == 0xa59;
      assert s1.Peek(11) == 0x60d;
      assert s1.Peek(16) == 0x2c0;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1028;
      assert s11.Peek(4) == 0x11fd;
      assert s11.Peek(7) == 0xa59;
      assert s11.Peek(11) == 0x60d;
      assert s11.Peek(16) == 0x2c0;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s13, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 220
    * Starting at 0x1028
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1028 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x11fd

    requires s0.stack[5] == 0xa59

    requires s0.stack[9] == 0x60d

    requires s0.stack[14] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11fd;
      assert s1.Peek(5) == 0xa59;
      assert s1.Peek(9) == 0x60d;
      assert s1.Peek(14) == 0x2c0;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s10, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 259
    * Starting at 0x11fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xa59

    requires s0.stack[7] == 0x60d

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa59;
      assert s1.Peek(7) == 0x60d;
      assert s1.Peek(12) == 0x2c0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s7, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 157
    * Starting at 0xa59
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x60d

    requires s0.stack[9] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60d;
      assert s1.Peek(9) == 0x2c0;
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

  /** Node 137
    * Segment Id for this node is: 158
    * Starting at 0xa62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x60d

    requires s0.stack[8] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x60d;
      assert s1.Peek(8) == 0x2c0;
      var s2 := Push2(s1, 0x0a6d);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e95);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s7, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 183
    * Starting at 0xe95
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe95 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xa6d

    requires s0.stack[7] == 0x60d

    requires s0.stack[12] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa6d;
      assert s1.Peek(7) == 0x60d;
      assert s1.Peek(12) == 0x2c0;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s5, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 159
    * Starting at 0xa6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x60d

    requires s0.stack[8] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x60d;
      assert s1.Peek(8) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x60d;
      assert s11.Peek(11) == 0x2c0;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x60d;
      assert s21.Peek(10) == 0x2c0;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0af3);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s29, gas - 1)
      else
        ExecuteFromCFGNode_s140(s29, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 160
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x60d

    requires s0.stack[9] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x60d;
      assert s1.Peek(10) == 0x2c0;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0aea);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1264);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s11, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 266
    * Starting at 0x1264
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1264 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xaea

    requires s0.stack[6] == 0x60d

    requires s0.stack[11] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaea;
      assert s1.Peek(6) == 0x60d;
      assert s1.Peek(11) == 0x2c0;
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
      assert s11.Peek(4) == 0xaea;
      assert s11.Peek(9) == 0x60d;
      assert s11.Peek(14) == 0x2c0;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x127d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x109c);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s18, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 230
    * Starting at 0x109c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x127d

    requires s0.stack[4] == 0xaea

    requires s0.stack[9] == 0x60d

    requires s0.stack[14] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x127d;
      assert s1.Peek(4) == 0xaea;
      assert s1.Peek(9) == 0x60d;
      assert s1.Peek(14) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10a9);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s7, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x10a9

    requires s0.stack[5] == 0x127d

    requires s0.stack[8] == 0xaea

    requires s0.stack[13] == 0x60d

    requires s0.stack[18] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10a9;
      assert s1.Peek(5) == 0x127d;
      assert s1.Peek(8) == 0xaea;
      assert s1.Peek(13) == 0x60d;
      assert s1.Peek(18) == 0x2c0;
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
      assert s11.Peek(0) == 0x10a9;
      assert s11.Peek(6) == 0x127d;
      assert s11.Peek(9) == 0xaea;
      assert s11.Peek(14) == 0x60d;
      assert s11.Peek(19) == 0x2c0;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s15, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 231
    * Starting at 0x10a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x127d

    requires s0.stack[6] == 0xaea

    requires s0.stack[11] == 0x60d

    requires s0.stack[16] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x127d;
      assert s1.Peek(6) == 0xaea;
      assert s1.Peek(11) == 0x60d;
      assert s1.Peek(16) == 0x2c0;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10b4);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x160b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s7, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 315
    * Starting at 0x160b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x10b4

    requires s0.stack[4] == 0x127d

    requires s0.stack[7] == 0xaea

    requires s0.stack[12] == 0x60d

    requires s0.stack[17] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10b4;
      assert s1.Peek(4) == 0x127d;
      assert s1.Peek(7) == 0xaea;
      assert s1.Peek(12) == 0x60d;
      assert s1.Peek(17) == 0x2c0;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x616c616e63650000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x10b4;
      assert s11.Peek(4) == 0x127d;
      assert s11.Peek(7) == 0xaea;
      assert s11.Peek(12) == 0x60d;
      assert s11.Peek(17) == 0x2c0;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s13, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 232
    * Starting at 0x10b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x127d

    requires s0.stack[5] == 0xaea

    requires s0.stack[10] == 0x60d

    requires s0.stack[15] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x127d;
      assert s1.Peek(5) == 0xaea;
      assert s1.Peek(10) == 0x60d;
      assert s1.Peek(15) == 0x2c0;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s10, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 267
    * Starting at 0x127d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xaea

    requires s0.stack[8] == 0x60d

    requires s0.stack[13] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaea;
      assert s1.Peek(8) == 0x60d;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s7, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 161
    * Starting at 0xaea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x60d

    requires s0.stack[10] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60d;
      assert s1.Peek(10) == 0x2c0;
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
    * Segment Id for this node is: 162
    * Starting at 0xaf3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x60d

    requires s0.stack[9] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60d;
      assert s1.Peek(9) == 0x2c0;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x60d;
      assert s11.Peek(13) == 0x2c0;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(7) == 0x60d;
      assert s21.Peek(12) == 0x2c0;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Dup2(s26);
      var s28 := Push1(s27, 0x00);
      var s29 := Dup1(s28);
      var s30 := Dup6(s29);
      var s31 := Push20(s30, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s31.Peek(9) == 0x60d;
      assert s31.Peek(14) == 0x2c0;
      var s32 := And(s31);
      var s33 := Push20(s32, 0xffffffffffffffffffffffffffffffffffffffff);
      var s34 := And(s33);
      var s35 := Dup2(s34);
      var s36 := MStore(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Add(s37);
      var s39 := Swap1(s38);
      var s40 := Dup2(s39);
      var s41 := MStore(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s150(s41, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 163
    * Starting at 0xb72
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x60d

    requires s0.stack[11] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x60d;
      assert s1.Peek(12) == 0x2c0;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Keccak256(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup3(s5);
      var s7 := Dup3(s6);
      var s8 := SLoad(s7);
      var s9 := Add(s8);
      var s10 := Swap3(s9);
      var s11 := Pop(s10);
      assert s11.Peek(7) == 0x60d;
      assert s11.Peek(12) == 0x2c0;
      var s12 := Pop(s11);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := SStore(s14);
      var s16 := Pop(s15);
      var s17 := Dup3(s16);
      var s18 := Push20(s17, 0xffffffffffffffffffffffffffffffffffffffff);
      var s19 := And(s18);
      var s20 := Dup5(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(7) == 0x60d;
      assert s21.Peek(12) == 0x2c0;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x0be1);
      var s28 := Swap2(s27);
      var s29 := Swap1(s28);
      var s30 := Push2(s29, 0x1324);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s31, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xbe1

    requires s0.stack[10] == 0x60d

    requires s0.stack[15] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbe1;
      assert s1.Peek(10) == 0x60d;
      assert s1.Peek(15) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0xbe1;
      assert s11.Peek(13) == 0x60d;
      assert s11.Peek(18) == 0x2c0;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s14, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0xbe1

    requires s0.stack[14] == 0x60d

    requires s0.stack[19] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0xbe1;
      assert s1.Peek(14) == 0x60d;
      assert s1.Peek(19) == 0x2c0;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s5, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0xbe1

    requires s0.stack[16] == 0x60d

    requires s0.stack[21] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0xbe1;
      assert s1.Peek(16) == 0x60d;
      assert s1.Peek(21) == 0x2c0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s9, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0xbe1

    requires s0.stack[15] == 0x60d

    requires s0.stack[20] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0xbe1;
      assert s1.Peek(15) == 0x60d;
      assert s1.Peek(20) == 0x2c0;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s6, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xbe1

    requires s0.stack[11] == 0x60d

    requires s0.stack[16] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbe1;
      assert s1.Peek(11) == 0x60d;
      assert s1.Peek(16) == 0x2c0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s6, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 164
    * Starting at 0xbe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x60d

    requires s0.stack[13] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x60d;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x0bf4);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(2) == 0xbf4;
      assert s11.Peek(7) == 0x60d;
      assert s11.Peek(12) == 0x2c0;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e9a);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s14, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 184
    * Starting at 0xe9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xbf4

    requires s0.stack[8] == 0x60d

    requires s0.stack[13] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbf4;
      assert s1.Peek(8) == 0x60d;
      assert s1.Peek(13) == 0x2c0;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s5, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 165
    * Starting at 0xbf4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x60d

    requires s0.stack[9] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60d;
      assert s1.Peek(9) == 0x2c0;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s6, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 125
    * Starting at 0x60d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x2c0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2c0;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s10, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 67
    * Starting at 0x2c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x02cd);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11a7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s8, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 254
    * Starting at 0x11a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2cd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2cd;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x11bc);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x11bc;
      assert s11.Peek(5) == 0x2cd;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0fc8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s14, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 211
    * Starting at 0xfc8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11bc

    requires s0.stack[6] == 0x2cd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11bc;
      assert s1.Peek(6) == 0x2cd;
      var s2 := Push2(s1, 0x0fd1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13de);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s5, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 292
    * Starting at 0x13de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfd1

    requires s0.stack[4] == 0x11bc

    requires s0.stack[8] == 0x2cd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfd1;
      assert s1.Peek(4) == 0x11bc;
      assert s1.Peek(8) == 0x2cd;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s11, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 212
    * Starting at 0xfd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11bc

    requires s0.stack[7] == 0x2cd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11bc;
      assert s1.Peek(7) == 0x2cd;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s6, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 255
    * Starting at 0x11bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x2cd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2cd;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s6, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 68
    * Starting at 0x2cd
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cd as nat
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

  /** Node 167
    * Segment Id for this node is: 61
    * Starting at 0x276
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x276 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0290);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x028b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x28b;
      assert s11.Peek(3) == 0x290;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f7d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s14, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 204
    * Starting at 0xf7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x28b

    requires s0.stack[3] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x28b;
      assert s1.Peek(3) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f90);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s11, gas - 1)
      else
        ExecuteFromCFGNode_s169(s11, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 205
    * Starting at 0xf8c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x28b

    requires s0.stack[5] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x28b;
      assert s1.Peek(6) == 0x290;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 170
    * Segment Id for this node is: 206
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x28b

    requires s0.stack[5] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x28b;
      assert s1.Peek(5) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f9e);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s9, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf9e

    requires s0.stack[8] == 0x28b

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9e;
      assert s1.Peek(8) == 0x28b;
      assert s1.Peek(9) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s10, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x28b

    requires s0.stack[12] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x28b;
      assert s1.Peek(12) == 0x290;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s5, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf9e

    requires s0.stack[13] == 0x28b

    requires s0.stack[14] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf9e;
      assert s1.Peek(13) == 0x28b;
      assert s1.Peek(14) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s6, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf9e

    requires s0.stack[16] == 0x28b

    requires s0.stack[17] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf9e;
      assert s1.Peek(16) == 0x28b;
      assert s1.Peek(17) == 0x290;
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
      ExecuteFromCFGNode_s175(s11, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf9e

    requires s0.stack[15] == 0x28b

    requires s0.stack[16] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf9e;
      assert s1.Peek(15) == 0x28b;
      assert s1.Peek(16) == 0x290;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s7, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf9e

    requires s0.stack[12] == 0x28b

    requires s0.stack[13] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x28b;
      assert s1.Peek(13) == 0x290;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s5, gas - 1)
      else
        ExecuteFromCFGNode_s177(s5, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x28b

    requires s0.stack[12] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x28b;
      assert s1.Peek(13) == 0x290;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 178
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x28b

    requires s0.stack[12] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x28b;
      assert s1.Peek(12) == 0x290;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s3, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf9e

    requires s0.stack[9] == 0x28b

    requires s0.stack[10] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9e;
      assert s1.Peek(9) == 0x28b;
      assert s1.Peek(10) == 0x290;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s6, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 207
    * Starting at 0xf9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x28b

    requires s0.stack[7] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x28b;
      assert s1.Peek(7) == 0x290;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0faf);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0eb4);
      assert s11.Peek(0) == 0xeb4;
      assert s11.Peek(3) == 0xfaf;
      assert s11.Peek(9) == 0x28b;
      assert s11.Peek(10) == 0x290;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s12, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 187
    * Starting at 0xeb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xfaf

    requires s0.stack[8] == 0x28b

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaf;
      assert s1.Peek(8) == 0x28b;
      assert s1.Peek(9) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ec3);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x17b0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s10, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 325
    * Starting at 0x17b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x28b

    requires s0.stack[12] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x28b;
      assert s1.Peek(12) == 0x290;
      var s2 := Push2(s1, 0x17b9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s5, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17b9

    requires s0.stack[3] == 0xec3

    requires s0.stack[7] == 0xfaf

    requires s0.stack[13] == 0x28b

    requires s0.stack[14] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17b9;
      assert s1.Peek(3) == 0xec3;
      assert s1.Peek(7) == 0xfaf;
      assert s1.Peek(13) == 0x28b;
      assert s1.Peek(14) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s9, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 326
    * Starting at 0x17b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xec3

    requires s0.stack[6] == 0xfaf

    requires s0.stack[12] == 0x28b

    requires s0.stack[13] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x28b;
      assert s1.Peek(13) == 0x290;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17c4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s5, gas - 1)
      else
        ExecuteFromCFGNode_s185(s5, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 327
    * Starting at 0x17c0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x28b

    requires s0.stack[12] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x28b;
      assert s1.Peek(13) == 0x290;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 186
    * Segment Id for this node is: 328
    * Starting at 0x17c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x28b

    requires s0.stack[12] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x28b;
      assert s1.Peek(12) == 0x290;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s3, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 188
    * Starting at 0xec3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xfaf

    requires s0.stack[9] == 0x28b

    requires s0.stack[10] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfaf;
      assert s1.Peek(9) == 0x28b;
      assert s1.Peek(10) == 0x290;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s6, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 208
    * Starting at 0xfaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x28b

    requires s0.stack[7] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x28b;
      assert s1.Peek(7) == 0x290;
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
      ExecuteFromCFGNode_s189(s10, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 62
    * Starting at 0x28b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x290;
      var s2 := Push2(s1, 0x057e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s3, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 116
    * Starting at 0x57e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0589);
      var s5 := Push2(s4, 0x0723);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s6, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 134
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x589

    requires s0.stack[5] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x589;
      assert s1.Peek(5) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s7, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 117
    * Starting at 0x589
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x589 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x290;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push2(s4, 0x0597);
      var s6 := Dup3(s5);
      var s7 := Dup7(s6);
      var s8 := Push2(s7, 0x0618);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s9, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 126
    * Starting at 0x618
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x618 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x597

    requires s0.stack[8] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x597;
      assert s1.Peek(8) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x597;
      assert s11.Peek(11) == 0x290;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x597;
      assert s21.Peek(11) == 0x290;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x597;
      assert s31.Peek(11) == 0x290;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s194(s41, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 127
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x597

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x597;
      assert s1.Peek(9) == 0x290;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s4, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 118
    * Starting at 0x597
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x597 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x290;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup4(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x05dc);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s205(s9, gas - 1)
      else
        ExecuteFromCFGNode_s196(s9, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 119
    * Starting at 0x5a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x290;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x05d3);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12e4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s11, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 274
    * Starting at 0x12e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x5d3

    requires s0.stack[7] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5d3;
      assert s1.Peek(7) == 0x290;
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
      assert s11.Peek(4) == 0x5d3;
      assert s11.Peek(10) == 0x290;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12fd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1128);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s18, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 242
    * Starting at 0x1128
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1128 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x12fd

    requires s0.stack[4] == 0x5d3

    requires s0.stack[10] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12fd;
      assert s1.Peek(4) == 0x5d3;
      assert s1.Peek(10) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1135);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s7, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x1135

    requires s0.stack[5] == 0x12fd

    requires s0.stack[8] == 0x5d3

    requires s0.stack[14] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1135;
      assert s1.Peek(5) == 0x12fd;
      assert s1.Peek(8) == 0x5d3;
      assert s1.Peek(14) == 0x290;
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
      assert s11.Peek(0) == 0x1135;
      assert s11.Peek(6) == 0x12fd;
      assert s11.Peek(9) == 0x5d3;
      assert s11.Peek(15) == 0x290;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s15, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 243
    * Starting at 0x1135
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x12fd

    requires s0.stack[6] == 0x5d3

    requires s0.stack[12] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12fd;
      assert s1.Peek(6) == 0x5d3;
      assert s1.Peek(12) == 0x290;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1140);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1721);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s7, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 319
    * Starting at 0x1721
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1721 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1140

    requires s0.stack[4] == 0x12fd

    requires s0.stack[7] == 0x5d3

    requires s0.stack[13] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1140;
      assert s1.Peek(4) == 0x12fd;
      assert s1.Peek(7) == 0x5d3;
      assert s1.Peek(13) == 0x290;
      var s2 := Push32(s1, 0x45524332303a2064656372656173656420616c6c6f77616e63652062656c6f77);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x207a65726f000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1140;
      assert s11.Peek(4) == 0x12fd;
      assert s11.Peek(7) == 0x5d3;
      assert s11.Peek(13) == 0x290;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s13, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 244
    * Starting at 0x1140
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x12fd

    requires s0.stack[5] == 0x5d3

    requires s0.stack[11] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12fd;
      assert s1.Peek(5) == 0x5d3;
      assert s1.Peek(11) == 0x290;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s10, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 275
    * Starting at 0x12fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5d3

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d3;
      assert s1.Peek(9) == 0x290;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s7, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 120
    * Starting at 0x5d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x290;
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

  /** Node 205
    * Segment Id for this node is: 121
    * Starting at 0x5dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x290;
      var s2 := Push2(s1, 0x05e9);
      var s3 := Dup3(s2);
      var s4 := Dup7(s3);
      var s5 := Dup7(s4);
      var s6 := Dup5(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x072b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s9, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 135
    * Starting at 0x72b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5e9

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5e9;
      assert s1.Peek(9) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x079b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s216(s11, gas - 1)
      else
        ExecuteFromCFGNode_s207(s11, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 136
    * Starting at 0x761
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x761 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5e9

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5e9;
      assert s1.Peek(10) == 0x290;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0792);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12c4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s11, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 272
    * Starting at 0x12c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x792

    requires s0.stack[5] == 0x5e9

    requires s0.stack[11] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x792;
      assert s1.Peek(5) == 0x5e9;
      assert s1.Peek(11) == 0x290;
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
      assert s11.Peek(4) == 0x792;
      assert s11.Peek(8) == 0x5e9;
      assert s11.Peek(14) == 0x290;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12dd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1105);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s18, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 239
    * Starting at 0x1105
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x12dd

    requires s0.stack[4] == 0x792

    requires s0.stack[8] == 0x5e9

    requires s0.stack[14] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12dd;
      assert s1.Peek(4) == 0x792;
      assert s1.Peek(8) == 0x5e9;
      assert s1.Peek(14) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1112);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s7, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1112

    requires s0.stack[5] == 0x12dd

    requires s0.stack[8] == 0x792

    requires s0.stack[12] == 0x5e9

    requires s0.stack[18] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1112;
      assert s1.Peek(5) == 0x12dd;
      assert s1.Peek(8) == 0x792;
      assert s1.Peek(12) == 0x5e9;
      assert s1.Peek(18) == 0x290;
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
      assert s11.Peek(0) == 0x1112;
      assert s11.Peek(6) == 0x12dd;
      assert s11.Peek(9) == 0x792;
      assert s11.Peek(13) == 0x5e9;
      assert s11.Peek(19) == 0x290;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s15, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 240
    * Starting at 0x1112
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1112 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x12dd

    requires s0.stack[6] == 0x792

    requires s0.stack[10] == 0x5e9

    requires s0.stack[16] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12dd;
      assert s1.Peek(6) == 0x792;
      assert s1.Peek(10) == 0x5e9;
      assert s1.Peek(16) == 0x290;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x111d);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x16d2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s7, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 318
    * Starting at 0x16d2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x111d

    requires s0.stack[4] == 0x12dd

    requires s0.stack[7] == 0x792

    requires s0.stack[11] == 0x5e9

    requires s0.stack[17] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x111d;
      assert s1.Peek(4) == 0x12dd;
      assert s1.Peek(7) == 0x792;
      assert s1.Peek(11) == 0x5e9;
      assert s1.Peek(17) == 0x290;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x111d;
      assert s11.Peek(4) == 0x12dd;
      assert s11.Peek(7) == 0x792;
      assert s11.Peek(11) == 0x5e9;
      assert s11.Peek(17) == 0x290;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s13, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 241
    * Starting at 0x111d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x12dd

    requires s0.stack[5] == 0x792

    requires s0.stack[9] == 0x5e9

    requires s0.stack[15] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12dd;
      assert s1.Peek(5) == 0x792;
      assert s1.Peek(9) == 0x5e9;
      assert s1.Peek(15) == 0x290;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s10, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 273
    * Starting at 0x12dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x792

    requires s0.stack[7] == 0x5e9

    requires s0.stack[13] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x792;
      assert s1.Peek(7) == 0x5e9;
      assert s1.Peek(13) == 0x290;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s7, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 137
    * Starting at 0x792
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x5e9

    requires s0.stack[10] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5e9;
      assert s1.Peek(10) == 0x290;
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

  /** Node 216
    * Segment Id for this node is: 138
    * Starting at 0x79b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5e9

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5e9;
      assert s1.Peek(9) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x080b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s11, gas - 1)
      else
        ExecuteFromCFGNode_s217(s11, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 139
    * Starting at 0x7d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5e9

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5e9;
      assert s1.Peek(10) == 0x290;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0802);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1224);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s11, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 262
    * Starting at 0x1224
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1224 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x802

    requires s0.stack[5] == 0x5e9

    requires s0.stack[11] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x802;
      assert s1.Peek(5) == 0x5e9;
      assert s1.Peek(11) == 0x290;
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
      assert s11.Peek(4) == 0x802;
      assert s11.Peek(8) == 0x5e9;
      assert s11.Peek(14) == 0x290;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x123d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1056);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s18, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 224
    * Starting at 0x1056
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1056 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x123d

    requires s0.stack[4] == 0x802

    requires s0.stack[8] == 0x5e9

    requires s0.stack[14] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x123d;
      assert s1.Peek(4) == 0x802;
      assert s1.Peek(8) == 0x5e9;
      assert s1.Peek(14) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1063);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s7, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1063

    requires s0.stack[5] == 0x123d

    requires s0.stack[8] == 0x802

    requires s0.stack[12] == 0x5e9

    requires s0.stack[18] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(5) == 0x123d;
      assert s1.Peek(8) == 0x802;
      assert s1.Peek(12) == 0x5e9;
      assert s1.Peek(18) == 0x290;
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
      assert s11.Peek(0) == 0x1063;
      assert s11.Peek(6) == 0x123d;
      assert s11.Peek(9) == 0x802;
      assert s11.Peek(13) == 0x5e9;
      assert s11.Peek(19) == 0x290;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s15, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 225
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x123d

    requires s0.stack[6] == 0x802

    requires s0.stack[10] == 0x5e9

    requires s0.stack[16] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x123d;
      assert s1.Peek(6) == 0x802;
      assert s1.Peek(10) == 0x5e9;
      assert s1.Peek(16) == 0x290;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x106e);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1593);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s7, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 313
    * Starting at 0x1593
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x106e

    requires s0.stack[4] == 0x123d

    requires s0.stack[7] == 0x802

    requires s0.stack[11] == 0x5e9

    requires s0.stack[17] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106e;
      assert s1.Peek(4) == 0x123d;
      assert s1.Peek(7) == 0x802;
      assert s1.Peek(11) == 0x5e9;
      assert s1.Peek(17) == 0x290;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x106e;
      assert s11.Peek(4) == 0x123d;
      assert s11.Peek(7) == 0x802;
      assert s11.Peek(11) == 0x5e9;
      assert s11.Peek(17) == 0x290;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s13, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 226
    * Starting at 0x106e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x123d

    requires s0.stack[5] == 0x802

    requires s0.stack[9] == 0x5e9

    requires s0.stack[15] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x123d;
      assert s1.Peek(5) == 0x802;
      assert s1.Peek(9) == 0x5e9;
      assert s1.Peek(15) == 0x290;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s10, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 263
    * Starting at 0x123d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x802

    requires s0.stack[7] == 0x5e9

    requires s0.stack[13] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x802;
      assert s1.Peek(7) == 0x5e9;
      assert s1.Peek(13) == 0x290;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s7, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 140
    * Starting at 0x802
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x802 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x5e9

    requires s0.stack[10] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5e9;
      assert s1.Peek(10) == 0x290;
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
    * Segment Id for this node is: 141
    * Starting at 0x80b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5e9

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5e9;
      assert s1.Peek(9) == 0x290;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x5e9;
      assert s11.Peek(12) == 0x290;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x5e9;
      assert s21.Peek(12) == 0x290;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x5e9;
      assert s31.Peek(12) == 0x290;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s227(s41, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 142
    * Starting at 0x88d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5e9

    requires s0.stack[9] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x5e9;
      assert s1.Peek(10) == 0x290;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08e9);
      assert s11.Peek(0) == 0x8e9;
      assert s11.Peek(9) == 0x5e9;
      assert s11.Peek(15) == 0x290;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x1324);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s15, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x8e9

    requires s0.stack[9] == 0x5e9

    requires s0.stack[15] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e9;
      assert s1.Peek(9) == 0x5e9;
      assert s1.Peek(15) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0x8e9;
      assert s11.Peek(12) == 0x5e9;
      assert s11.Peek(18) == 0x290;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s14, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0x8e9

    requires s0.stack[13] == 0x5e9

    requires s0.stack[19] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0x8e9;
      assert s1.Peek(13) == 0x5e9;
      assert s1.Peek(19) == 0x290;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s5, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0x8e9

    requires s0.stack[15] == 0x5e9

    requires s0.stack[21] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0x8e9;
      assert s1.Peek(15) == 0x5e9;
      assert s1.Peek(21) == 0x290;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s9, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0x8e9

    requires s0.stack[14] == 0x5e9

    requires s0.stack[20] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0x8e9;
      assert s1.Peek(14) == 0x5e9;
      assert s1.Peek(20) == 0x290;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s6, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x8e9

    requires s0.stack[10] == 0x5e9

    requires s0.stack[16] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8e9;
      assert s1.Peek(10) == 0x5e9;
      assert s1.Peek(16) == 0x290;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s6, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 143
    * Starting at 0x8e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x5e9

    requires s0.stack[13] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5e9;
      assert s1.Peek(13) == 0x290;
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
      assert s11.Peek(0) == 0x5e9;
      assert s11.Peek(6) == 0x290;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s12, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 122
    * Starting at 0x5e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x290

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x290;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s11, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 63
    * Starting at 0x290
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x290 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x029d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11a7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s8, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 254
    * Starting at 0x11a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x29d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x29d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x11bc);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x11bc;
      assert s11.Peek(5) == 0x29d;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0fc8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s14, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 211
    * Starting at 0xfc8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11bc

    requires s0.stack[6] == 0x29d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11bc;
      assert s1.Peek(6) == 0x29d;
      var s2 := Push2(s1, 0x0fd1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13de);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s5, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 292
    * Starting at 0x13de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfd1

    requires s0.stack[4] == 0x11bc

    requires s0.stack[8] == 0x29d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfd1;
      assert s1.Peek(4) == 0x11bc;
      assert s1.Peek(8) == 0x29d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s11, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 212
    * Starting at 0xfd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11bc

    requires s0.stack[7] == 0x29d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11bc;
      assert s1.Peek(7) == 0x29d;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s6, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 255
    * Starting at 0x11bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x29d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x29d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s6, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 64
    * Starting at 0x29d
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29d as nat
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

  /** Node 242
    * Segment Id for this node is: 10
    * Starting at 0x66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x70a08231);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0200);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s320(s6, gas - 1)
      else
        ExecuteFromCFGNode_s243(s6, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 11
    * Starting at 0x72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0230);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s298(s5, gas - 1)
      else
        ExecuteFromCFGNode_s244(s5, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x023a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s5, gas - 1)
      else
        ExecuteFromCFGNode_s245(s5, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0258);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s247(s5, gas - 1)
      else
        ExecuteFromCFGNode_s246(s5, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 14
    * Starting at 0x93
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00f5);
      assert s1.Peek(0) == 0xf5;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 58
    * Starting at 0x258
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x258 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0260);
      var s3 := Push2(s2, 0x04ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s4, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 107
    * Starting at 0x4ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x260;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x04fb);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x1454);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s9, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 302
    * Starting at 0x1454
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1454 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x4fb

    requires s0.stack[4] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4fb;
      assert s1.Peek(4) == 0x260;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x4fb;
      assert s11.Peek(7) == 0x260;
      var s12 := Push2(s11, 0x146c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s251(s13, gas - 1)
      else
        ExecuteFromCFGNode_s250(s13, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 303
    * Starting at 0x1466
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1466 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4fb

    requires s0.stack[6] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x4fb;
      assert s1.Peek(7) == 0x260;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s251(s5, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 304
    * Starting at 0x146c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4fb

    requires s0.stack[6] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4fb;
      assert s1.Peek(6) == 0x260;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1480);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s254(s9, gas - 1)
      else
        ExecuteFromCFGNode_s252(s9, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 305
    * Starting at 0x1478
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1478 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4fb

    requires s0.stack[6] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x147f);
      assert s1.Peek(0) == 0x147f;
      assert s1.Peek(4) == 0x4fb;
      assert s1.Peek(7) == 0x260;
      var s2 := Push2(s1, 0x14b5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s3, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 309
    * Starting at 0x14b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x147f

    requires s0.stack[4] == 0x4fb

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x147f;
      assert s1.Peek(4) == 0x4fb;
      assert s1.Peek(7) == 0x260;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 254
    * Segment Id for this node is: 307
    * Starting at 0x1480
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1480 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4fb

    requires s0.stack[6] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4fb;
      assert s1.Peek(6) == 0x260;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s6, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 108
    * Starting at 0x4fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x260;
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
      assert s11.Peek(4) == 0x260;
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
      assert s21.Peek(5) == 0x260;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x0527);
      assert s31.Peek(0) == 0x527;
      assert s31.Peek(8) == 0x260;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x1454);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s34, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 302
    * Starting at 0x1454
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1454 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x527

    requires s0.stack[8] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x527;
      assert s1.Peek(8) == 0x260;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x527;
      assert s11.Peek(11) == 0x260;
      var s12 := Push2(s11, 0x146c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s13, gas - 1)
      else
        ExecuteFromCFGNode_s257(s13, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 303
    * Starting at 0x1466
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1466 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x527

    requires s0.stack[10] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x527;
      assert s1.Peek(11) == 0x260;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s258(s5, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 304
    * Starting at 0x146c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x527

    requires s0.stack[10] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x527;
      assert s1.Peek(10) == 0x260;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1480);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s9, gas - 1)
      else
        ExecuteFromCFGNode_s259(s9, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 305
    * Starting at 0x1478
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1478 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x527

    requires s0.stack[10] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x147f);
      assert s1.Peek(0) == 0x147f;
      assert s1.Peek(4) == 0x527;
      assert s1.Peek(11) == 0x260;
      var s2 := Push2(s1, 0x14b5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s3, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 309
    * Starting at 0x14b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x147f

    requires s0.stack[4] == 0x527

    requires s0.stack[11] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x147f;
      assert s1.Peek(4) == 0x527;
      assert s1.Peek(11) == 0x260;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 261
    * Segment Id for this node is: 307
    * Starting at 0x1480
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1480 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x527

    requires s0.stack[10] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x527;
      assert s1.Peek(10) == 0x260;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s6, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 109
    * Starting at 0x527
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x527 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x260;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0574);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s265(s5, gas - 1)
      else
        ExecuteFromCFGNode_s263(s5, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 110
    * Starting at 0x52e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x260;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0549);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s284(s5, gas - 1)
      else
        ExecuteFromCFGNode_s264(s5, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 111
    * Starting at 0x536
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x260;
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
      assert s11.Peek(7) == 0x260;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0574);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s14, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 115
    * Starting at 0x574
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x574 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x260;
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
      ExecuteFromCFGNode_s266(s10, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 59
    * Starting at 0x260
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x026d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11c2);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s267(s8, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 256
    * Starting at 0x11c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x26d;
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
      assert s11.Peek(5) == 0x26d;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x11dc);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0fd7);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s19, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 213
    * Starting at 0xfd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11dc

    requires s0.stack[6] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11dc;
      assert s1.Peek(6) == 0x26d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0fe2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x135a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s6, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 282
    * Starting at 0x135a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xfe2

    requires s0.stack[5] == 0x11dc

    requires s0.stack[9] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfe2;
      assert s1.Peek(5) == 0x11dc;
      assert s1.Peek(9) == 0x26d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s10, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 214
    * Starting at 0xfe2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x11dc

    requires s0.stack[8] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x11dc;
      assert s1.Peek(8) == 0x26d;
      var s2 := Push2(s1, 0x0fec);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x1365);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s6, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xfec

    requires s0.stack[7] == 0x11dc

    requires s0.stack[11] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfec;
      assert s1.Peek(7) == 0x11dc;
      assert s1.Peek(11) == 0x26d;
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
      assert s11.Peek(0) == 0xfec;
      assert s11.Peek(8) == 0x11dc;
      assert s11.Peek(12) == 0x26d;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s15, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 215
    * Starting at 0xfec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x11dc

    requires s0.stack[9] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11dc;
      assert s1.Peek(9) == 0x26d;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0ffc);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x1421);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s11, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 296
    * Starting at 0x1421
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1421 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xffc

    requires s0.stack[8] == 0x11dc

    requires s0.stack[12] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xffc;
      assert s1.Peek(8) == 0x11dc;
      assert s1.Peek(12) == 0x26d;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s274(s2, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 297
    * Starting at 0x1424
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1424 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xffc;
      assert s1.Peek(9) == 0x11dc;
      assert s1.Peek(13) == 0x26d;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x143f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s276(s7, gas - 1)
      else
        ExecuteFromCFGNode_s275(s7, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 298
    * Starting at 0x142d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x142d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xffc;
      assert s1.Peek(10) == 0x11dc;
      assert s1.Peek(14) == 0x26d;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0xffc;
      assert s11.Peek(10) == 0x11dc;
      assert s11.Peek(14) == 0x26d;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x1424);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s15, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 299
    * Starting at 0x143f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xffc;
      assert s1.Peek(9) == 0x11dc;
      assert s1.Peek(13) == 0x26d;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x144e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s278(s7, gas - 1)
      else
        ExecuteFromCFGNode_s277(s7, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 300
    * Starting at 0x1448
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1448 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xffc;
      assert s1.Peek(10) == 0x11dc;
      assert s1.Peek(14) == 0x26d;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s278(s5, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 301
    * Starting at 0x144e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x144e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xffc;
      assert s1.Peek(9) == 0x11dc;
      assert s1.Peek(13) == 0x26d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s6, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 216
    * Starting at 0xffc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x11dc

    requires s0.stack[8] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x11dc;
      assert s1.Peek(8) == 0x26d;
      var s2 := Push2(s1, 0x1005);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x14e4);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s5, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 310
    * Starting at 0x14e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1005

    requires s0.stack[6] == 0x11dc

    requires s0.stack[10] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1005;
      assert s1.Peek(6) == 0x11dc;
      assert s1.Peek(10) == 0x26d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1005;
      assert s11.Peek(7) == 0x11dc;
      assert s11.Peek(11) == 0x26d;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s14, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 217
    * Starting at 0x1005
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1005 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x11dc

    requires s0.stack[9] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11dc;
      assert s1.Peek(9) == 0x26d;
      var s2 := Dup5(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s11, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 257
    * Starting at 0x11dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x26d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x26d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s8, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 60
    * Starting at 0x26d
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26d as nat
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

  /** Node 284
    * Segment Id for this node is: 112
    * Starting at 0x549
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x549 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x260;
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
      ExecuteFromCFGNode_s285(s11, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 113
    * Starting at 0x557
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x557 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x260;
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
      assert s11.Peek(7) == 0x260;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x0557);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s285(s16, gas - 1)
      else
        ExecuteFromCFGNode_s286(s16, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 114
    * Starting at 0x56b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x260;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s265(s8, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 55
    * Starting at 0x23a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0242);
      var s3 := Push2(s2, 0x04c2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s4, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 106
    * Starting at 0x4c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x242;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x242;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s17, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 56
    * Starting at 0x242
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x242 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x024f);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x118c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s290(s8, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 252
    * Starting at 0x118c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x11a1);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x11a1;
      assert s11.Peek(5) == 0x24f;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0fb9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s14, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 209
    * Starting at 0xfb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11a1

    requires s0.stack[6] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11a1;
      assert s1.Peek(6) == 0x24f;
      var s2 := Push2(s1, 0x0fc2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s5, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfc2

    requires s0.stack[4] == 0x11a1

    requires s0.stack[8] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfc2;
      assert s1.Peek(4) == 0x11a1;
      assert s1.Peek(8) == 0x24f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s293(s6, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0xfc2

    requires s0.stack[7] == 0x11a1

    requires s0.stack[11] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0xfc2;
      assert s1.Peek(7) == 0x11a1;
      assert s1.Peek(11) == 0x24f;
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
      ExecuteFromCFGNode_s294(s11, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xfc2

    requires s0.stack[6] == 0x11a1

    requires s0.stack[10] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfc2;
      assert s1.Peek(6) == 0x11a1;
      assert s1.Peek(10) == 0x24f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s7, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 210
    * Starting at 0xfc2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11a1

    requires s0.stack[7] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11a1;
      assert s1.Peek(7) == 0x24f;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s6, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 253
    * Starting at 0x11a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x24f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s6, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 57
    * Starting at 0x24f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24f as nat
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

  /** Node 298
    * Segment Id for this node is: 53
    * Starting at 0x230
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x230 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0238);
      var s3 := Push2(s2, 0x04ae);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s4, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 103
    * Starting at 0x4ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x238;
      var s2 := Push2(s1, 0x04b6);
      var s3 := Push2(s2, 0x0bfa);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s4, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 166
    * Starting at 0xbfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b6

    requires s0.stack[1] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4b6;
      assert s1.Peek(1) == 0x238;
      var s2 := Push2(s1, 0x0c02);
      var s3 := Push2(s2, 0x0723);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s4, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 134
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0xc02

    requires s0.stack[1] == 0x4b6

    requires s0.stack[2] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc02;
      assert s1.Peek(1) == 0x4b6;
      assert s1.Peek(2) == 0x238;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s7, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 167
    * Starting at 0xc02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4b6

    requires s0.stack[2] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b6;
      assert s1.Peek(2) == 0x238;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0c20);
      var s5 := Push2(s4, 0x04c2);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s303(s6, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 106
    * Starting at 0x4c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0xc20

    requires s0.stack[2] == 0x4b6

    requires s0.stack[3] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc20;
      assert s1.Peek(2) == 0x4b6;
      assert s1.Peek(3) == 0x238;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0xc20;
      assert s11.Peek(4) == 0x4b6;
      assert s11.Peek(5) == 0x238;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s17, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 168
    * Starting at 0xc20
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x4b6

    requires s0.stack[3] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4b6;
      assert s1.Peek(3) == 0x238;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0c76);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s314(s6, gas - 1)
      else
        ExecuteFromCFGNode_s305(s6, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 169
    * Starting at 0xc3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b6

    requires s0.stack[1] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x4b6;
      assert s1.Peek(2) == 0x238;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c6d);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1284);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s11, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 268
    * Starting at 0x1284
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1284 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0xc6d

    requires s0.stack[2] == 0x4b6

    requires s0.stack[3] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6d;
      assert s1.Peek(2) == 0x4b6;
      assert s1.Peek(3) == 0x238;
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
      assert s11.Peek(4) == 0xc6d;
      assert s11.Peek(5) == 0x4b6;
      assert s11.Peek(6) == 0x238;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x129d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10bf);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s18, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 233
    * Starting at 0x10bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x129d

    requires s0.stack[4] == 0xc6d

    requires s0.stack[5] == 0x4b6

    requires s0.stack[6] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x129d;
      assert s1.Peek(4) == 0xc6d;
      assert s1.Peek(5) == 0x4b6;
      assert s1.Peek(6) == 0x238;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10cc);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s7, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x10cc

    requires s0.stack[5] == 0x129d

    requires s0.stack[8] == 0xc6d

    requires s0.stack[9] == 0x4b6

    requires s0.stack[10] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10cc;
      assert s1.Peek(5) == 0x129d;
      assert s1.Peek(8) == 0xc6d;
      assert s1.Peek(9) == 0x4b6;
      assert s1.Peek(10) == 0x238;
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
      assert s11.Peek(0) == 0x10cc;
      assert s11.Peek(6) == 0x129d;
      assert s11.Peek(9) == 0xc6d;
      assert s11.Peek(10) == 0x4b6;
      assert s11.Peek(11) == 0x238;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s15, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 234
    * Starting at 0x10cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x129d

    requires s0.stack[6] == 0xc6d

    requires s0.stack[7] == 0x4b6

    requires s0.stack[8] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x129d;
      assert s1.Peek(6) == 0xc6d;
      assert s1.Peek(7) == 0x4b6;
      assert s1.Peek(8) == 0x238;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10d7);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x165a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s7, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 316
    * Starting at 0x165a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x165a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x10d7

    requires s0.stack[4] == 0x129d

    requires s0.stack[7] == 0xc6d

    requires s0.stack[8] == 0x4b6

    requires s0.stack[9] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d7;
      assert s1.Peek(4) == 0x129d;
      assert s1.Peek(7) == 0xc6d;
      assert s1.Peek(8) == 0x4b6;
      assert s1.Peek(9) == 0x238;
      var s2 := Push32(s1, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s8, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 235
    * Starting at 0x10d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x129d

    requires s0.stack[5] == 0xc6d

    requires s0.stack[6] == 0x4b6

    requires s0.stack[7] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x129d;
      assert s1.Peek(5) == 0xc6d;
      assert s1.Peek(6) == 0x4b6;
      assert s1.Peek(7) == 0x238;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s10, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 269
    * Starting at 0x129d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0xc6d

    requires s0.stack[4] == 0x4b6

    requires s0.stack[5] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc6d;
      assert s1.Peek(4) == 0x4b6;
      assert s1.Peek(5) == 0x238;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s7, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 170
    * Starting at 0xc6d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4b6

    requires s0.stack[2] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b6;
      assert s1.Peek(2) == 0x238;
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

  /** Node 314
    * Segment Id for this node is: 171
    * Starting at 0xc76
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b6

    requires s0.stack[1] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4b6;
      assert s1.Peek(1) == 0x238;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s2, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 104
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x238;
      var s2 := Push2(s1, 0x04c0);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0dcf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s5, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 181
    * Starting at 0xdcf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4c0

    requires s0.stack[2] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4c0;
      assert s1.Peek(2) == 0x238;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x4c0;
      assert s11.Peek(4) == 0x238;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x05);
      var s18 := Push1(s17, 0x00);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x4c0;
      assert s21.Peek(7) == 0x238;
      var s22 := SLoad(s21);
      var s23 := Dup2(s22);
      var s24 := Push20(s23, 0xffffffffffffffffffffffffffffffffffffffff);
      var s25 := Mul(s24);
      var s26 := Not(s25);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Dup4(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(7) == 0x4c0;
      assert s31.Peek(8) == 0x238;
      var s32 := Mul(s31);
      var s33 := Or(s32);
      var s34 := Swap1(s33);
      var s35 := SStore(s34);
      var s36 := Pop(s35);
      var s37 := Dup2(s36);
      var s38 := Push20(s37, 0xffffffffffffffffffffffffffffffffffffffff);
      var s39 := And(s38);
      var s40 := Dup2(s39);
      var s41 := Push20(s40, 0xffffffffffffffffffffffffffffffffffffffff);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s317(s41, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 182
    * Starting at 0xe65
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x4c0

    requires s0.stack[6] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x4c0;
      assert s1.Peek(5) == 0x238;
      var s2 := Push32(s1, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Swap2(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Log3(s10);
      assert s11.Peek(2) == 0x4c0;
      assert s11.Peek(3) == 0x238;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s14, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 105
    * Starting at 0x4c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x238

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x238;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s319(s2, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 54
    * Starting at 0x238
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x238 as nat
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

  /** Node 320
    * Segment Id for this node is: 49
    * Starting at 0x200
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x200 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x021a);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0215);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x215;
      assert s11.Peek(3) == 0x21a;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0ec9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s14, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 189
    * Starting at 0xec9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x215

    requires s0.stack[3] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x215;
      assert s1.Peek(3) == 0x21a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0edb);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s323(s10, gas - 1)
      else
        ExecuteFromCFGNode_s322(s10, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 190
    * Starting at 0xed7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x215

    requires s0.stack[4] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x215;
      assert s1.Peek(5) == 0x21a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 323
    * Segment Id for this node is: 191
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x215

    requires s0.stack[4] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x215;
      assert s1.Peek(4) == 0x21a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ee9);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s324(s9, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xee9

    requires s0.stack[7] == 0x215

    requires s0.stack[8] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xee9;
      assert s1.Peek(7) == 0x215;
      assert s1.Peek(8) == 0x21a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s10, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xee9

    requires s0.stack[10] == 0x215

    requires s0.stack[11] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xee9;
      assert s1.Peek(10) == 0x215;
      assert s1.Peek(11) == 0x21a;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s5, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xee9

    requires s0.stack[12] == 0x215

    requires s0.stack[13] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xee9;
      assert s1.Peek(12) == 0x215;
      assert s1.Peek(13) == 0x21a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s6, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xee9

    requires s0.stack[15] == 0x215

    requires s0.stack[16] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xee9;
      assert s1.Peek(15) == 0x215;
      assert s1.Peek(16) == 0x21a;
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
      ExecuteFromCFGNode_s328(s11, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xee9

    requires s0.stack[14] == 0x215

    requires s0.stack[15] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xee9;
      assert s1.Peek(14) == 0x215;
      assert s1.Peek(15) == 0x21a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s329(s7, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xee9

    requires s0.stack[11] == 0x215

    requires s0.stack[12] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xee9;
      assert s1.Peek(11) == 0x215;
      assert s1.Peek(12) == 0x21a;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s331(s5, gas - 1)
      else
        ExecuteFromCFGNode_s330(s5, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xee9

    requires s0.stack[10] == 0x215

    requires s0.stack[11] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xee9;
      assert s1.Peek(11) == 0x215;
      assert s1.Peek(12) == 0x21a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 331
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xee9

    requires s0.stack[10] == 0x215

    requires s0.stack[11] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xee9;
      assert s1.Peek(10) == 0x215;
      assert s1.Peek(11) == 0x21a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s3, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xee9

    requires s0.stack[8] == 0x215

    requires s0.stack[9] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee9;
      assert s1.Peek(8) == 0x215;
      assert s1.Peek(9) == 0x21a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s333(s6, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 192
    * Starting at 0xee9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x215

    requires s0.stack[6] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x215;
      assert s1.Peek(6) == 0x21a;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s9, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 50
    * Starting at 0x215
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x215 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x21a;
      var s2 := Push2(s1, 0x0466);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s3, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 102
    * Starting at 0x466
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x466 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x21a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x21a;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(3) == 0x21a;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Swap2(s23);
      var s25 := Swap1(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s27, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 51
    * Starting at 0x21a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0227);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1324);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s8, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x227

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x227;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0x227;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s338(s14, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0x227

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0x227;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s5, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0x227

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0x227;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s340(s9, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0x227

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0x227;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s6, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x227

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x227;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s6, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 52
    * Starting at 0x227
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x227 as nat
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

  /** Node 343
    * Segment Id for this node is: 15
    * Starting at 0x97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s637(s6, gas - 1)
      else
        ExecuteFromCFGNode_s344(s6, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 16
    * Starting at 0xa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
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
      var s4 := Push2(s3, 0x0166);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s505(s5, gas - 1)
      else
        ExecuteFromCFGNode_s345(s5, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 17
    * Starting at 0xae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
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
      var s4 := Push2(s3, 0x0196);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s496(s5, gas - 1)
      else
        ExecuteFromCFGNode_s346(s5, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 18
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
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
      var s4 := Push2(s3, 0x01b4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s422(s5, gas - 1)
      else
        ExecuteFromCFGNode_s347(s5, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 19
    * Starting at 0xc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x40c10f19);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01e4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s349(s5, gas - 1)
      else
        ExecuteFromCFGNode_s348(s5, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 20
    * Starting at 0xcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00f5);
      assert s1.Peek(0) == 0xf5;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 46
    * Starting at 0x1e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01fe);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01f9);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1f9;
      assert s11.Peek(3) == 0x1fe;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f7d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s14, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 204
    * Starting at 0xf7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1f9

    requires s0.stack[3] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1f9;
      assert s1.Peek(3) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f90);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s352(s11, gas - 1)
      else
        ExecuteFromCFGNode_s351(s11, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 205
    * Starting at 0xf8c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1f9

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1f9;
      assert s1.Peek(6) == 0x1fe;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 352
    * Segment Id for this node is: 206
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1f9

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1f9;
      assert s1.Peek(5) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f9e);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s9, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf9e

    requires s0.stack[8] == 0x1f9

    requires s0.stack[9] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9e;
      assert s1.Peek(8) == 0x1f9;
      assert s1.Peek(9) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s10, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x1f9

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x1f9;
      assert s1.Peek(12) == 0x1fe;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s5, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf9e

    requires s0.stack[13] == 0x1f9

    requires s0.stack[14] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf9e;
      assert s1.Peek(13) == 0x1f9;
      assert s1.Peek(14) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s6, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf9e

    requires s0.stack[16] == 0x1f9

    requires s0.stack[17] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf9e;
      assert s1.Peek(16) == 0x1f9;
      assert s1.Peek(17) == 0x1fe;
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
      ExecuteFromCFGNode_s357(s11, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf9e

    requires s0.stack[15] == 0x1f9

    requires s0.stack[16] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf9e;
      assert s1.Peek(15) == 0x1f9;
      assert s1.Peek(16) == 0x1fe;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s7, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf9e

    requires s0.stack[12] == 0x1f9

    requires s0.stack[13] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x1f9;
      assert s1.Peek(13) == 0x1fe;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s360(s5, gas - 1)
      else
        ExecuteFromCFGNode_s359(s5, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x1f9

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x1f9;
      assert s1.Peek(13) == 0x1fe;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 360
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x1f9

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x1f9;
      assert s1.Peek(12) == 0x1fe;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s361(s3, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf9e

    requires s0.stack[9] == 0x1f9

    requires s0.stack[10] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9e;
      assert s1.Peek(9) == 0x1f9;
      assert s1.Peek(10) == 0x1fe;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s6, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 207
    * Starting at 0xf9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1f9

    requires s0.stack[7] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1f9;
      assert s1.Peek(7) == 0x1fe;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0faf);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0eb4);
      assert s11.Peek(0) == 0xeb4;
      assert s11.Peek(3) == 0xfaf;
      assert s11.Peek(9) == 0x1f9;
      assert s11.Peek(10) == 0x1fe;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s12, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 187
    * Starting at 0xeb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xfaf

    requires s0.stack[8] == 0x1f9

    requires s0.stack[9] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaf;
      assert s1.Peek(8) == 0x1f9;
      assert s1.Peek(9) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ec3);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x17b0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s364(s10, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 325
    * Starting at 0x17b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x1f9

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x1f9;
      assert s1.Peek(12) == 0x1fe;
      var s2 := Push2(s1, 0x17b9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s5, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17b9

    requires s0.stack[3] == 0xec3

    requires s0.stack[7] == 0xfaf

    requires s0.stack[13] == 0x1f9

    requires s0.stack[14] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17b9;
      assert s1.Peek(3) == 0xec3;
      assert s1.Peek(7) == 0xfaf;
      assert s1.Peek(13) == 0x1f9;
      assert s1.Peek(14) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s366(s9, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 326
    * Starting at 0x17b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xec3

    requires s0.stack[6] == 0xfaf

    requires s0.stack[12] == 0x1f9

    requires s0.stack[13] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x1f9;
      assert s1.Peek(13) == 0x1fe;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17c4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s368(s5, gas - 1)
      else
        ExecuteFromCFGNode_s367(s5, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 327
    * Starting at 0x17c0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x1f9

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x1f9;
      assert s1.Peek(13) == 0x1fe;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 368
    * Segment Id for this node is: 328
    * Starting at 0x17c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x1f9

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x1f9;
      assert s1.Peek(12) == 0x1fe;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s3, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 188
    * Starting at 0xec3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xfaf

    requires s0.stack[9] == 0x1f9

    requires s0.stack[10] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfaf;
      assert s1.Peek(9) == 0x1f9;
      assert s1.Peek(10) == 0x1fe;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s6, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 208
    * Starting at 0xfaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1f9

    requires s0.stack[7] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1f9;
      assert s1.Peek(7) == 0x1fe;
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
      ExecuteFromCFGNode_s371(s10, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 47
    * Starting at 0x1f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fe;
      var s2 := Push2(s1, 0x0450);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s3, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 99
    * Starting at 0x450
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fe;
      var s2 := Push2(s1, 0x0458);
      var s3 := Push2(s2, 0x0bfa);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s4, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 166
    * Starting at 0xbfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x458

    requires s0.stack[3] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x458;
      assert s1.Peek(3) == 0x1fe;
      var s2 := Push2(s1, 0x0c02);
      var s3 := Push2(s2, 0x0723);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s4, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 134
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0xc02

    requires s0.stack[1] == 0x458

    requires s0.stack[4] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc02;
      assert s1.Peek(1) == 0x458;
      assert s1.Peek(4) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s7, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 167
    * Starting at 0xc02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x458

    requires s0.stack[4] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x458;
      assert s1.Peek(4) == 0x1fe;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0c20);
      var s5 := Push2(s4, 0x04c2);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s376(s6, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 106
    * Starting at 0x4c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xc20

    requires s0.stack[2] == 0x458

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc20;
      assert s1.Peek(2) == 0x458;
      assert s1.Peek(5) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0xc20;
      assert s11.Peek(4) == 0x458;
      assert s11.Peek(7) == 0x1fe;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s17, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 168
    * Starting at 0xc20
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x458

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x458;
      assert s1.Peek(5) == 0x1fe;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0c76);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s387(s6, gas - 1)
      else
        ExecuteFromCFGNode_s378(s6, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 169
    * Starting at 0xc3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x458

    requires s0.stack[3] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x458;
      assert s1.Peek(4) == 0x1fe;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c6d);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1284);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s11, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 268
    * Starting at 0x1284
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1284 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0xc6d

    requires s0.stack[2] == 0x458

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6d;
      assert s1.Peek(2) == 0x458;
      assert s1.Peek(5) == 0x1fe;
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
      assert s11.Peek(4) == 0xc6d;
      assert s11.Peek(5) == 0x458;
      assert s11.Peek(8) == 0x1fe;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x129d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10bf);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s18, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 233
    * Starting at 0x10bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x129d

    requires s0.stack[4] == 0xc6d

    requires s0.stack[5] == 0x458

    requires s0.stack[8] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x129d;
      assert s1.Peek(4) == 0xc6d;
      assert s1.Peek(5) == 0x458;
      assert s1.Peek(8) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10cc);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s7, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x10cc

    requires s0.stack[5] == 0x129d

    requires s0.stack[8] == 0xc6d

    requires s0.stack[9] == 0x458

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10cc;
      assert s1.Peek(5) == 0x129d;
      assert s1.Peek(8) == 0xc6d;
      assert s1.Peek(9) == 0x458;
      assert s1.Peek(12) == 0x1fe;
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
      assert s11.Peek(0) == 0x10cc;
      assert s11.Peek(6) == 0x129d;
      assert s11.Peek(9) == 0xc6d;
      assert s11.Peek(10) == 0x458;
      assert s11.Peek(13) == 0x1fe;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s15, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 234
    * Starting at 0x10cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x129d

    requires s0.stack[6] == 0xc6d

    requires s0.stack[7] == 0x458

    requires s0.stack[10] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x129d;
      assert s1.Peek(6) == 0xc6d;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(10) == 0x1fe;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10d7);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x165a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s7, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 316
    * Starting at 0x165a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x165a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x10d7

    requires s0.stack[4] == 0x129d

    requires s0.stack[7] == 0xc6d

    requires s0.stack[8] == 0x458

    requires s0.stack[11] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d7;
      assert s1.Peek(4) == 0x129d;
      assert s1.Peek(7) == 0xc6d;
      assert s1.Peek(8) == 0x458;
      assert s1.Peek(11) == 0x1fe;
      var s2 := Push32(s1, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s384(s8, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 235
    * Starting at 0x10d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x129d

    requires s0.stack[5] == 0xc6d

    requires s0.stack[6] == 0x458

    requires s0.stack[9] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x129d;
      assert s1.Peek(5) == 0xc6d;
      assert s1.Peek(6) == 0x458;
      assert s1.Peek(9) == 0x1fe;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s10, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 269
    * Starting at 0x129d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xc6d

    requires s0.stack[4] == 0x458

    requires s0.stack[7] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc6d;
      assert s1.Peek(4) == 0x458;
      assert s1.Peek(7) == 0x1fe;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s7, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 170
    * Starting at 0xc6d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x458

    requires s0.stack[4] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x458;
      assert s1.Peek(4) == 0x1fe;
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

  /** Node 387
    * Segment Id for this node is: 171
    * Starting at 0xc76
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x458

    requires s0.stack[3] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x458;
      assert s1.Peek(3) == 0x1fe;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s388(s2, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 100
    * Starting at 0x458
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x458 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fe;
      var s2 := Push2(s1, 0x0462);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c78);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s389(s6, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 172
    * Starting at 0xc78
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x462

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x462;
      assert s1.Peek(5) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0ce8);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s399(s11, gas - 1)
      else
        ExecuteFromCFGNode_s390(s11, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 173
    * Starting at 0xcae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x462

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x462;
      assert s1.Peek(6) == 0x1fe;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0cdf);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1304);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s391(s11, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 276
    * Starting at 0x1304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xcdf

    requires s0.stack[4] == 0x462

    requires s0.stack[7] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcdf;
      assert s1.Peek(4) == 0x462;
      assert s1.Peek(7) == 0x1fe;
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
      assert s11.Peek(4) == 0xcdf;
      assert s11.Peek(7) == 0x462;
      assert s11.Peek(10) == 0x1fe;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x131d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x114b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s18, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 245
    * Starting at 0x114b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x131d

    requires s0.stack[4] == 0xcdf

    requires s0.stack[7] == 0x462

    requires s0.stack[10] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x131d;
      assert s1.Peek(4) == 0xcdf;
      assert s1.Peek(7) == 0x462;
      assert s1.Peek(10) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1158);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s7, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x1158

    requires s0.stack[5] == 0x131d

    requires s0.stack[8] == 0xcdf

    requires s0.stack[11] == 0x462

    requires s0.stack[14] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1158;
      assert s1.Peek(5) == 0x131d;
      assert s1.Peek(8) == 0xcdf;
      assert s1.Peek(11) == 0x462;
      assert s1.Peek(14) == 0x1fe;
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
      assert s11.Peek(0) == 0x1158;
      assert s11.Peek(6) == 0x131d;
      assert s11.Peek(9) == 0xcdf;
      assert s11.Peek(12) == 0x462;
      assert s11.Peek(15) == 0x1fe;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s15, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 246
    * Starting at 0x1158
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1158 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x131d

    requires s0.stack[6] == 0xcdf

    requires s0.stack[9] == 0x462

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x131d;
      assert s1.Peek(6) == 0xcdf;
      assert s1.Peek(9) == 0x462;
      assert s1.Peek(12) == 0x1fe;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1163);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1770);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s7, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 320
    * Starting at 0x1770
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1770 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1163

    requires s0.stack[4] == 0x131d

    requires s0.stack[7] == 0xcdf

    requires s0.stack[10] == 0x462

    requires s0.stack[13] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1163;
      assert s1.Peek(4) == 0x131d;
      assert s1.Peek(7) == 0xcdf;
      assert s1.Peek(10) == 0x462;
      assert s1.Peek(13) == 0x1fe;
      var s2 := Push32(s1, 0x45524332303a206d696e7420746f20746865207a65726f206164647265737300);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s8, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 247
    * Starting at 0x1163
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1163 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x131d

    requires s0.stack[5] == 0xcdf

    requires s0.stack[8] == 0x462

    requires s0.stack[11] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x131d;
      assert s1.Peek(5) == 0xcdf;
      assert s1.Peek(8) == 0x462;
      assert s1.Peek(11) == 0x1fe;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s10, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 277
    * Starting at 0x131d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xcdf

    requires s0.stack[6] == 0x462

    requires s0.stack[9] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcdf;
      assert s1.Peek(6) == 0x462;
      assert s1.Peek(9) == 0x1fe;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s7, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 174
    * Starting at 0xcdf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x462

    requires s0.stack[6] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x462;
      assert s1.Peek(6) == 0x1fe;
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

  /** Node 399
    * Segment Id for this node is: 175
    * Starting at 0xce8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x462

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x462;
      assert s1.Peek(5) == 0x1fe;
      var s2 := Push2(s1, 0x0cf4);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e95);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s400(s7, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 183
    * Starting at 0xe95
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe95 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xcf4

    requires s0.stack[6] == 0x462

    requires s0.stack[9] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcf4;
      assert s1.Peek(6) == 0x462;
      assert s1.Peek(9) == 0x1fe;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s5, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 176
    * Starting at 0xcf4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x462

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x462;
      assert s1.Peek(5) == 0x1fe;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := SLoad(s6);
      var s8 := Push2(s7, 0x0d06);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x1376);
      assert s11.Peek(0) == 0x1376;
      assert s11.Peek(3) == 0xd06;
      assert s11.Peek(9) == 0x462;
      assert s11.Peek(12) == 0x1fe;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s402(s12, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 284
    * Starting at 0x1376
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1376 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xd06

    requires s0.stack[8] == 0x462

    requires s0.stack[11] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd06;
      assert s1.Peek(8) == 0x462;
      assert s1.Peek(11) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1381);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x140a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s6, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1381

    requires s0.stack[5] == 0xd06

    requires s0.stack[11] == 0x462

    requires s0.stack[14] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1381;
      assert s1.Peek(5) == 0xd06;
      assert s1.Peek(11) == 0x462;
      assert s1.Peek(14) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s9, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 285
    * Starting at 0x1381
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1381 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd06

    requires s0.stack[10] == 0x462

    requires s0.stack[13] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd06;
      assert s1.Peek(10) == 0x462;
      assert s1.Peek(13) == 0x1fe;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x138c);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x140a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s7, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x138c

    requires s0.stack[5] == 0xd06

    requires s0.stack[11] == 0x462

    requires s0.stack[14] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x138c;
      assert s1.Peek(5) == 0xd06;
      assert s1.Peek(11) == 0x462;
      assert s1.Peek(14) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s9, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 286
    * Starting at 0x138c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x138c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd06

    requires s0.stack[10] == 0x462

    requires s0.stack[13] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd06;
      assert s1.Peek(10) == 0x462;
      assert s1.Peek(13) == 0x1fe;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x13c1);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s409(s11, gas - 1)
      else
        ExecuteFromCFGNode_s407(s11, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 287
    * Starting at 0x13b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xd06

    requires s0.stack[9] == 0x462

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x13c0);
      assert s1.Peek(0) == 0x13c0;
      assert s1.Peek(4) == 0xd06;
      assert s1.Peek(10) == 0x462;
      assert s1.Peek(13) == 0x1fe;
      var s2 := Push2(s1, 0x1486);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s3, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 308
    * Starting at 0x1486
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1486 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x13c0

    requires s0.stack[4] == 0xd06

    requires s0.stack[10] == 0x462

    requires s0.stack[13] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x13c0;
      assert s1.Peek(4) == 0xd06;
      assert s1.Peek(10) == 0x462;
      assert s1.Peek(13) == 0x1fe;
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

  /** Node 409
    * Segment Id for this node is: 289
    * Starting at 0x13c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xd06

    requires s0.stack[9] == 0x462

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd06;
      assert s1.Peek(9) == 0x462;
      assert s1.Peek(12) == 0x1fe;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s11, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 177
    * Starting at 0xd06
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x462

    requires s0.stack[9] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x462;
      assert s1.Peek(9) == 0x1fe;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup1(s10);
      assert s11.Peek(5) == 0x462;
      assert s11.Peek(8) == 0x1fe;
      var s12 := Dup5(s11);
      var s13 := Push20(s12, 0xffffffffffffffffffffffffffffffffffffffff);
      var s14 := And(s13);
      var s15 := Push20(s14, 0xffffffffffffffffffffffffffffffffffffffff);
      var s16 := And(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x462;
      assert s21.Peek(8) == 0x1fe;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x20);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0x00);
      var s27 := Keccak256(s26);
      var s28 := Push1(s27, 0x00);
      var s29 := Dup3(s28);
      var s30 := Dup3(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(7) == 0x462;
      assert s31.Peek(10) == 0x1fe;
      var s32 := Add(s31);
      var s33 := Swap3(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Dup2(s35);
      var s37 := Swap1(s36);
      var s38 := SStore(s37);
      var s39 := Pop(s38);
      var s40 := Dup2(s39);
      var s41 := Push20(s40, 0xffffffffffffffffffffffffffffffffffffffff);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s411(s41, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 178
    * Starting at 0xd70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x462

    requires s0.stack[7] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(3) == 0x462;
      assert s1.Peek(6) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push32(s4, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push2(s8, 0x0db7);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xdb7;
      assert s11.Peek(8) == 0x462;
      assert s11.Peek(11) == 0x1fe;
      var s12 := Push2(s11, 0x1324);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s13, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xdb7

    requires s0.stack[8] == 0x462

    requires s0.stack[11] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb7;
      assert s1.Peek(8) == 0x462;
      assert s1.Peek(11) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0xdb7;
      assert s11.Peek(11) == 0x462;
      assert s11.Peek(14) == 0x1fe;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s14, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0xdb7

    requires s0.stack[12] == 0x462

    requires s0.stack[15] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0xdb7;
      assert s1.Peek(12) == 0x462;
      assert s1.Peek(15) == 0x1fe;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s5, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0xdb7

    requires s0.stack[14] == 0x462

    requires s0.stack[17] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0xdb7;
      assert s1.Peek(14) == 0x462;
      assert s1.Peek(17) == 0x1fe;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s9, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0xdb7

    requires s0.stack[13] == 0x462

    requires s0.stack[16] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0xdb7;
      assert s1.Peek(13) == 0x462;
      assert s1.Peek(16) == 0x1fe;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s6, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xdb7

    requires s0.stack[9] == 0x462

    requires s0.stack[12] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb7;
      assert s1.Peek(9) == 0x462;
      assert s1.Peek(12) == 0x1fe;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s6, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 179
    * Starting at 0xdb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x462

    requires s0.stack[9] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x462;
      assert s1.Peek(9) == 0x1fe;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x0dcb);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup4(s10);
      assert s11.Peek(2) == 0xdcb;
      assert s11.Peek(5) == 0x462;
      assert s11.Peek(8) == 0x1fe;
      var s12 := Dup4(s11);
      var s13 := Push2(s12, 0x0e9a);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s14, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 184
    * Starting at 0xe9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xdcb

    requires s0.stack[6] == 0x462

    requires s0.stack[9] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdcb;
      assert s1.Peek(6) == 0x462;
      assert s1.Peek(9) == 0x1fe;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s419(s5, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 180
    * Starting at 0xdcb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x462

    requires s0.stack[5] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x462;
      assert s1.Peek(5) == 0x1fe;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s4, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 101
    * Starting at 0x462
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x462 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1fe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fe;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s4, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 48
    * Starting at 0x1fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fe as nat
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

  /** Node 422
    * Segment Id for this node is: 42
    * Starting at 0x1b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01ce);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01c9);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1c9;
      assert s11.Peek(3) == 0x1ce;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f7d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s14, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 204
    * Starting at 0xf7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1c9

    requires s0.stack[3] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c9;
      assert s1.Peek(3) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f90);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s425(s11, gas - 1)
      else
        ExecuteFromCFGNode_s424(s11, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 205
    * Starting at 0xf8c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c9

    requires s0.stack[5] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1c9;
      assert s1.Peek(6) == 0x1ce;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 425
    * Segment Id for this node is: 206
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c9

    requires s0.stack[5] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1c9;
      assert s1.Peek(5) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f9e);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s426(s9, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf9e

    requires s0.stack[8] == 0x1c9

    requires s0.stack[9] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9e;
      assert s1.Peek(8) == 0x1c9;
      assert s1.Peek(9) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s427(s10, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x1c9

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x1c9;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s428(s5, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf9e

    requires s0.stack[13] == 0x1c9

    requires s0.stack[14] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf9e;
      assert s1.Peek(13) == 0x1c9;
      assert s1.Peek(14) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s429(s6, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf9e

    requires s0.stack[16] == 0x1c9

    requires s0.stack[17] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf9e;
      assert s1.Peek(16) == 0x1c9;
      assert s1.Peek(17) == 0x1ce;
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
      ExecuteFromCFGNode_s430(s11, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf9e

    requires s0.stack[15] == 0x1c9

    requires s0.stack[16] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf9e;
      assert s1.Peek(15) == 0x1c9;
      assert s1.Peek(16) == 0x1ce;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s431(s7, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf9e

    requires s0.stack[12] == 0x1c9

    requires s0.stack[13] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x1c9;
      assert s1.Peek(13) == 0x1ce;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s433(s5, gas - 1)
      else
        ExecuteFromCFGNode_s432(s5, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x1c9

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x1c9;
      assert s1.Peek(13) == 0x1ce;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 433
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x1c9

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x1c9;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s3, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf9e

    requires s0.stack[9] == 0x1c9

    requires s0.stack[10] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9e;
      assert s1.Peek(9) == 0x1c9;
      assert s1.Peek(10) == 0x1ce;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s6, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 207
    * Starting at 0xf9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1c9

    requires s0.stack[7] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1c9;
      assert s1.Peek(7) == 0x1ce;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0faf);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0eb4);
      assert s11.Peek(0) == 0xeb4;
      assert s11.Peek(3) == 0xfaf;
      assert s11.Peek(9) == 0x1c9;
      assert s11.Peek(10) == 0x1ce;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s12, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 187
    * Starting at 0xeb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xfaf

    requires s0.stack[8] == 0x1c9

    requires s0.stack[9] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaf;
      assert s1.Peek(8) == 0x1c9;
      assert s1.Peek(9) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ec3);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x17b0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s437(s10, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 325
    * Starting at 0x17b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x1c9

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x1c9;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Push2(s1, 0x17b9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s438(s5, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17b9

    requires s0.stack[3] == 0xec3

    requires s0.stack[7] == 0xfaf

    requires s0.stack[13] == 0x1c9

    requires s0.stack[14] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17b9;
      assert s1.Peek(3) == 0xec3;
      assert s1.Peek(7) == 0xfaf;
      assert s1.Peek(13) == 0x1c9;
      assert s1.Peek(14) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s9, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 326
    * Starting at 0x17b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xec3

    requires s0.stack[6] == 0xfaf

    requires s0.stack[12] == 0x1c9

    requires s0.stack[13] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x1c9;
      assert s1.Peek(13) == 0x1ce;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17c4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s441(s5, gas - 1)
      else
        ExecuteFromCFGNode_s440(s5, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 327
    * Starting at 0x17c0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x1c9

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x1c9;
      assert s1.Peek(13) == 0x1ce;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 441
    * Segment Id for this node is: 328
    * Starting at 0x17c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x1c9

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x1c9;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s3, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 188
    * Starting at 0xec3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xfaf

    requires s0.stack[9] == 0x1c9

    requires s0.stack[10] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfaf;
      assert s1.Peek(9) == 0x1c9;
      assert s1.Peek(10) == 0x1ce;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s6, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 208
    * Starting at 0xfaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1c9

    requires s0.stack[7] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1c9;
      assert s1.Peek(7) == 0x1ce;
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
      ExecuteFromCFGNode_s444(s10, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 43
    * Starting at 0x1c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ce;
      var s2 := Push2(s1, 0x0419);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s3, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 94
    * Starting at 0x419
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x419 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0424);
      var s5 := Push2(s4, 0x0723);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s6, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 134
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x424

    requires s0.stack[5] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x424;
      assert s1.Peek(5) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s447(s7, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 95
    * Starting at 0x424
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x424 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1ce;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0445);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x0436);
      var s9 := Dup6(s8);
      var s10 := Dup10(s9);
      var s11 := Push2(s10, 0x0618);
      assert s11.Peek(0) == 0x618;
      assert s11.Peek(3) == 0x436;
      assert s11.Peek(7) == 0x445;
      assert s11.Peek(12) == 0x1ce;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s12, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 126
    * Starting at 0x618
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x618 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x436

    requires s0.stack[6] == 0x445

    requires s0.stack[11] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x436;
      assert s1.Peek(6) == 0x445;
      assert s1.Peek(11) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x436;
      assert s11.Peek(9) == 0x445;
      assert s11.Peek(14) == 0x1ce;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x436;
      assert s21.Peek(9) == 0x445;
      assert s21.Peek(14) == 0x1ce;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x436;
      assert s31.Peek(9) == 0x445;
      assert s31.Peek(14) == 0x1ce;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s449(s41, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 127
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x436

    requires s0.stack[7] == 0x445

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x436;
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s4, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 96
    * Starting at 0x436
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x436 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x445

    requires s0.stack[9] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x1ce;
      var s2 := Push2(s1, 0x0440);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x1376);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s6, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 284
    * Starting at 0x1376
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1376 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x440

    requires s0.stack[5] == 0x445

    requires s0.stack[10] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x440;
      assert s1.Peek(5) == 0x445;
      assert s1.Peek(10) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1381);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x140a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s6, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1381

    requires s0.stack[5] == 0x440

    requires s0.stack[8] == 0x445

    requires s0.stack[13] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1381;
      assert s1.Peek(5) == 0x440;
      assert s1.Peek(8) == 0x445;
      assert s1.Peek(13) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s9, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 285
    * Starting at 0x1381
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1381 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x440

    requires s0.stack[7] == 0x445

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x440;
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x138c);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x140a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s7, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x138c

    requires s0.stack[5] == 0x440

    requires s0.stack[8] == 0x445

    requires s0.stack[13] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x138c;
      assert s1.Peek(5) == 0x440;
      assert s1.Peek(8) == 0x445;
      assert s1.Peek(13) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s455(s9, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 286
    * Starting at 0x138c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x138c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x440

    requires s0.stack[7] == 0x445

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x440;
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x13c1);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s458(s11, gas - 1)
      else
        ExecuteFromCFGNode_s456(s11, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 287
    * Starting at 0x13b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x440

    requires s0.stack[6] == 0x445

    requires s0.stack[11] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x13c0);
      assert s1.Peek(0) == 0x13c0;
      assert s1.Peek(4) == 0x440;
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Push2(s1, 0x1486);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s457(s3, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 308
    * Starting at 0x1486
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1486 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x13c0

    requires s0.stack[4] == 0x440

    requires s0.stack[7] == 0x445

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x13c0;
      assert s1.Peek(4) == 0x440;
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(12) == 0x1ce;
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

  /** Node 458
    * Segment Id for this node is: 289
    * Starting at 0x13c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x440

    requires s0.stack[6] == 0x445

    requires s0.stack[11] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x440;
      assert s1.Peek(6) == 0x445;
      assert s1.Peek(11) == 0x1ce;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s11, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 97
    * Starting at 0x440
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x440 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x445;
      assert s1.Peek(8) == 0x1ce;
      var s2 := Push2(s1, 0x072b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s3, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 135
    * Starting at 0x72b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x445;
      assert s1.Peek(8) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x079b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s470(s11, gas - 1)
      else
        ExecuteFromCFGNode_s461(s11, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 136
    * Starting at 0x761
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x761 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x1ce;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0792);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12c4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s11, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 272
    * Starting at 0x12c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x792

    requires s0.stack[5] == 0x445

    requires s0.stack[10] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x792;
      assert s1.Peek(5) == 0x445;
      assert s1.Peek(10) == 0x1ce;
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
      assert s11.Peek(4) == 0x792;
      assert s11.Peek(8) == 0x445;
      assert s11.Peek(13) == 0x1ce;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12dd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1105);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s463(s18, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 239
    * Starting at 0x1105
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x12dd

    requires s0.stack[4] == 0x792

    requires s0.stack[8] == 0x445

    requires s0.stack[13] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12dd;
      assert s1.Peek(4) == 0x792;
      assert s1.Peek(8) == 0x445;
      assert s1.Peek(13) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1112);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s7, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1112

    requires s0.stack[5] == 0x12dd

    requires s0.stack[8] == 0x792

    requires s0.stack[12] == 0x445

    requires s0.stack[17] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1112;
      assert s1.Peek(5) == 0x12dd;
      assert s1.Peek(8) == 0x792;
      assert s1.Peek(12) == 0x445;
      assert s1.Peek(17) == 0x1ce;
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
      assert s11.Peek(0) == 0x1112;
      assert s11.Peek(6) == 0x12dd;
      assert s11.Peek(9) == 0x792;
      assert s11.Peek(13) == 0x445;
      assert s11.Peek(18) == 0x1ce;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s15, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 240
    * Starting at 0x1112
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1112 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x12dd

    requires s0.stack[6] == 0x792

    requires s0.stack[10] == 0x445

    requires s0.stack[15] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12dd;
      assert s1.Peek(6) == 0x792;
      assert s1.Peek(10) == 0x445;
      assert s1.Peek(15) == 0x1ce;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x111d);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x16d2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s466(s7, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 318
    * Starting at 0x16d2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x111d

    requires s0.stack[4] == 0x12dd

    requires s0.stack[7] == 0x792

    requires s0.stack[11] == 0x445

    requires s0.stack[16] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x111d;
      assert s1.Peek(4) == 0x12dd;
      assert s1.Peek(7) == 0x792;
      assert s1.Peek(11) == 0x445;
      assert s1.Peek(16) == 0x1ce;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x111d;
      assert s11.Peek(4) == 0x12dd;
      assert s11.Peek(7) == 0x792;
      assert s11.Peek(11) == 0x445;
      assert s11.Peek(16) == 0x1ce;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s467(s13, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 241
    * Starting at 0x111d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x12dd

    requires s0.stack[5] == 0x792

    requires s0.stack[9] == 0x445

    requires s0.stack[14] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12dd;
      assert s1.Peek(5) == 0x792;
      assert s1.Peek(9) == 0x445;
      assert s1.Peek(14) == 0x1ce;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s468(s10, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 273
    * Starting at 0x12dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x792

    requires s0.stack[7] == 0x445

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x792;
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s7, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 137
    * Starting at 0x792
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x445

    requires s0.stack[9] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x1ce;
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

  /** Node 470
    * Segment Id for this node is: 138
    * Starting at 0x79b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x445;
      assert s1.Peek(8) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x080b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s480(s11, gas - 1)
      else
        ExecuteFromCFGNode_s471(s11, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 139
    * Starting at 0x7d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x1ce;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0802);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1224);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s11, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 262
    * Starting at 0x1224
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1224 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x802

    requires s0.stack[5] == 0x445

    requires s0.stack[10] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x802;
      assert s1.Peek(5) == 0x445;
      assert s1.Peek(10) == 0x1ce;
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
      assert s11.Peek(4) == 0x802;
      assert s11.Peek(8) == 0x445;
      assert s11.Peek(13) == 0x1ce;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x123d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1056);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s18, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 224
    * Starting at 0x1056
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1056 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x123d

    requires s0.stack[4] == 0x802

    requires s0.stack[8] == 0x445

    requires s0.stack[13] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x123d;
      assert s1.Peek(4) == 0x802;
      assert s1.Peek(8) == 0x445;
      assert s1.Peek(13) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1063);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s474(s7, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1063

    requires s0.stack[5] == 0x123d

    requires s0.stack[8] == 0x802

    requires s0.stack[12] == 0x445

    requires s0.stack[17] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(5) == 0x123d;
      assert s1.Peek(8) == 0x802;
      assert s1.Peek(12) == 0x445;
      assert s1.Peek(17) == 0x1ce;
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
      assert s11.Peek(0) == 0x1063;
      assert s11.Peek(6) == 0x123d;
      assert s11.Peek(9) == 0x802;
      assert s11.Peek(13) == 0x445;
      assert s11.Peek(18) == 0x1ce;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s475(s15, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 225
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x123d

    requires s0.stack[6] == 0x802

    requires s0.stack[10] == 0x445

    requires s0.stack[15] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x123d;
      assert s1.Peek(6) == 0x802;
      assert s1.Peek(10) == 0x445;
      assert s1.Peek(15) == 0x1ce;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x106e);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1593);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s7, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 313
    * Starting at 0x1593
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x106e

    requires s0.stack[4] == 0x123d

    requires s0.stack[7] == 0x802

    requires s0.stack[11] == 0x445

    requires s0.stack[16] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106e;
      assert s1.Peek(4) == 0x123d;
      assert s1.Peek(7) == 0x802;
      assert s1.Peek(11) == 0x445;
      assert s1.Peek(16) == 0x1ce;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x106e;
      assert s11.Peek(4) == 0x123d;
      assert s11.Peek(7) == 0x802;
      assert s11.Peek(11) == 0x445;
      assert s11.Peek(16) == 0x1ce;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s477(s13, gas - 1)
  }

  /** Node 477
    * Segment Id for this node is: 226
    * Starting at 0x106e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x123d

    requires s0.stack[5] == 0x802

    requires s0.stack[9] == 0x445

    requires s0.stack[14] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x123d;
      assert s1.Peek(5) == 0x802;
      assert s1.Peek(9) == 0x445;
      assert s1.Peek(14) == 0x1ce;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s478(s10, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 263
    * Starting at 0x123d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x802

    requires s0.stack[7] == 0x445

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x802;
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(12) == 0x1ce;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s479(s7, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 140
    * Starting at 0x802
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x802 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x445

    requires s0.stack[9] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x1ce;
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

  /** Node 480
    * Segment Id for this node is: 141
    * Starting at 0x80b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x445;
      assert s1.Peek(8) == 0x1ce;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x445;
      assert s11.Peek(11) == 0x1ce;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x445;
      assert s21.Peek(11) == 0x1ce;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x445;
      assert s31.Peek(11) == 0x1ce;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s481(s41, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 142
    * Starting at 0x88d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x1ce;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08e9);
      assert s11.Peek(0) == 0x8e9;
      assert s11.Peek(9) == 0x445;
      assert s11.Peek(14) == 0x1ce;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x1324);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s15, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x8e9

    requires s0.stack[9] == 0x445

    requires s0.stack[14] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e9;
      assert s1.Peek(9) == 0x445;
      assert s1.Peek(14) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0x8e9;
      assert s11.Peek(12) == 0x445;
      assert s11.Peek(17) == 0x1ce;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s14, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0x8e9

    requires s0.stack[13] == 0x445

    requires s0.stack[18] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0x8e9;
      assert s1.Peek(13) == 0x445;
      assert s1.Peek(18) == 0x1ce;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s484(s5, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0x8e9

    requires s0.stack[15] == 0x445

    requires s0.stack[20] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0x8e9;
      assert s1.Peek(15) == 0x445;
      assert s1.Peek(20) == 0x1ce;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s9, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0x8e9

    requires s0.stack[14] == 0x445

    requires s0.stack[19] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0x8e9;
      assert s1.Peek(14) == 0x445;
      assert s1.Peek(19) == 0x1ce;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s486(s6, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x8e9

    requires s0.stack[10] == 0x445

    requires s0.stack[15] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8e9;
      assert s1.Peek(10) == 0x445;
      assert s1.Peek(15) == 0x1ce;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s487(s6, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 143
    * Starting at 0x8e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x445

    requires s0.stack[12] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(12) == 0x1ce;
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
      assert s11.Peek(0) == 0x445;
      assert s11.Peek(5) == 0x1ce;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s488(s12, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 98
    * Starting at 0x445
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x445 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1ce;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s10, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 44
    * Starting at 0x1ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01db);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11a7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s8, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 254
    * Starting at 0x11a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x11bc);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x11bc;
      assert s11.Peek(5) == 0x1db;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0fc8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s14, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 211
    * Starting at 0xfc8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11bc

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11bc;
      assert s1.Peek(6) == 0x1db;
      var s2 := Push2(s1, 0x0fd1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13de);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s5, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 292
    * Starting at 0x13de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfd1

    requires s0.stack[4] == 0x11bc

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfd1;
      assert s1.Peek(4) == 0x11bc;
      assert s1.Peek(8) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s493(s11, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 212
    * Starting at 0xfd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11bc

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11bc;
      assert s1.Peek(7) == 0x1db;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s494(s6, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 255
    * Starting at 0x11bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1db;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s6, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 45
    * Starting at 0x1db
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1db as nat
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

  /** Node 496
    * Segment Id for this node is: 39
    * Starting at 0x196
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x196 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x019e);
      var s3 := Push2(s2, 0x0410);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s497(s4, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 93
    * Starting at 0x410
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x410 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x19e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x19e;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x12);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s7, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 40
    * Starting at 0x19e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01ab);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x133f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s8, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 280
    * Starting at 0x133f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x133f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1ab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ab;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1354);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1354;
      assert s11.Peek(5) == 0x1ab;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x117d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s14, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 250
    * Starting at 0x117d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1354

    requires s0.stack[6] == 0x1ab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1354;
      assert s1.Peek(6) == 0x1ab;
      var s2 := Push2(s1, 0x1186);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1414);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s5, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 295
    * Starting at 0x1414
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1414 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1186

    requires s0.stack[4] == 0x1354

    requires s0.stack[8] == 0x1ab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1186;
      assert s1.Peek(4) == 0x1354;
      assert s1.Peek(8) == 0x1ab;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0xff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s11, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 251
    * Starting at 0x1186
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1186 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1354

    requires s0.stack[7] == 0x1ab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1354;
      assert s1.Peek(7) == 0x1ab;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s503(s6, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 281
    * Starting at 0x1354
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1354 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1ab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ab;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s504(s6, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 41
    * Starting at 0x1ab
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ab as nat
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

  /** Node 505
    * Segment Id for this node is: 35
    * Starting at 0x166
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x166 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0180);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x017b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x17b;
      assert s11.Peek(3) == 0x180;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f2e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s506(s14, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 198
    * Starting at 0xf2e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x17b

    requires s0.stack[3] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x17b;
      assert s1.Peek(3) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0f43);
      assert s11.Peek(0) == 0xf43;
      assert s11.Peek(7) == 0x17b;
      assert s11.Peek(8) == 0x180;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s508(s12, gas - 1)
      else
        ExecuteFromCFGNode_s507(s12, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 199
    * Starting at 0xf3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x17b

    requires s0.stack[6] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x17b;
      assert s1.Peek(7) == 0x180;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 508
    * Segment Id for this node is: 200
    * Starting at 0xf43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x17b

    requires s0.stack[6] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x17b;
      assert s1.Peek(6) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f51);
      var s4 := Dup7(s3);
      var s5 := Dup3(s4);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s509(s9, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xf51

    requires s0.stack[9] == 0x17b

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf51;
      assert s1.Peek(9) == 0x17b;
      assert s1.Peek(10) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s10, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf51

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf51;
      assert s1.Peek(12) == 0x17b;
      assert s1.Peek(13) == 0x180;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s511(s5, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf51

    requires s0.stack[14] == 0x17b

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf51;
      assert s1.Peek(14) == 0x17b;
      assert s1.Peek(15) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s6, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf51

    requires s0.stack[17] == 0x17b

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf51;
      assert s1.Peek(17) == 0x17b;
      assert s1.Peek(18) == 0x180;
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
      ExecuteFromCFGNode_s513(s11, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf51

    requires s0.stack[16] == 0x17b

    requires s0.stack[17] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf51;
      assert s1.Peek(16) == 0x17b;
      assert s1.Peek(17) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s514(s7, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf51

    requires s0.stack[13] == 0x17b

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf51;
      assert s1.Peek(13) == 0x17b;
      assert s1.Peek(14) == 0x180;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s516(s5, gas - 1)
      else
        ExecuteFromCFGNode_s515(s5, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf51

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf51;
      assert s1.Peek(13) == 0x17b;
      assert s1.Peek(14) == 0x180;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 516
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf51

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf51;
      assert s1.Peek(12) == 0x17b;
      assert s1.Peek(13) == 0x180;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s517(s3, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xf51

    requires s0.stack[10] == 0x17b

    requires s0.stack[11] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf51;
      assert s1.Peek(10) == 0x17b;
      assert s1.Peek(11) == 0x180;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s518(s6, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 201
    * Starting at 0xf51
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf51 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x17b

    requires s0.stack[8] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x17b;
      assert s1.Peek(8) == 0x180;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0f62);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0e9f);
      assert s11.Peek(0) == 0xe9f;
      assert s11.Peek(3) == 0xf62;
      assert s11.Peek(10) == 0x17b;
      assert s11.Peek(11) == 0x180;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s519(s12, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xf62

    requires s0.stack[9] == 0x17b

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf62;
      assert s1.Peek(9) == 0x17b;
      assert s1.Peek(10) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s10, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf62

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf62;
      assert s1.Peek(12) == 0x17b;
      assert s1.Peek(13) == 0x180;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s521(s5, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf62

    requires s0.stack[14] == 0x17b

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf62;
      assert s1.Peek(14) == 0x17b;
      assert s1.Peek(15) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s522(s6, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf62

    requires s0.stack[17] == 0x17b

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf62;
      assert s1.Peek(17) == 0x17b;
      assert s1.Peek(18) == 0x180;
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
      ExecuteFromCFGNode_s523(s11, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf62

    requires s0.stack[16] == 0x17b

    requires s0.stack[17] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf62;
      assert s1.Peek(16) == 0x17b;
      assert s1.Peek(17) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s524(s7, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf62

    requires s0.stack[13] == 0x17b

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf62;
      assert s1.Peek(13) == 0x17b;
      assert s1.Peek(14) == 0x180;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s526(s5, gas - 1)
      else
        ExecuteFromCFGNode_s525(s5, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf62

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf62;
      assert s1.Peek(13) == 0x17b;
      assert s1.Peek(14) == 0x180;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 526
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf62

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf62;
      assert s1.Peek(12) == 0x17b;
      assert s1.Peek(13) == 0x180;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s3, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xf62

    requires s0.stack[10] == 0x17b

    requires s0.stack[11] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf62;
      assert s1.Peek(10) == 0x17b;
      assert s1.Peek(11) == 0x180;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s528(s6, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 202
    * Starting at 0xf62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x17b

    requires s0.stack[8] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x17b;
      assert s1.Peek(8) == 0x180;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Push2(s5, 0x0f73);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0eb4);
      assert s11.Peek(0) == 0xeb4;
      assert s11.Peek(3) == 0xf73;
      assert s11.Peek(10) == 0x17b;
      assert s11.Peek(11) == 0x180;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s529(s12, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 187
    * Starting at 0xeb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xf73

    requires s0.stack[9] == 0x17b

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf73;
      assert s1.Peek(9) == 0x17b;
      assert s1.Peek(10) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ec3);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x17b0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s530(s10, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 325
    * Starting at 0x17b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xf73

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xf73;
      assert s1.Peek(12) == 0x17b;
      assert s1.Peek(13) == 0x180;
      var s2 := Push2(s1, 0x17b9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s531(s5, gas - 1)
  }

  /** Node 531
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x17b9

    requires s0.stack[3] == 0xec3

    requires s0.stack[7] == 0xf73

    requires s0.stack[14] == 0x17b

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17b9;
      assert s1.Peek(3) == 0xec3;
      assert s1.Peek(7) == 0xf73;
      assert s1.Peek(14) == 0x17b;
      assert s1.Peek(15) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s532(s9, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 326
    * Starting at 0x17b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xec3

    requires s0.stack[6] == 0xf73

    requires s0.stack[13] == 0x17b

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xf73;
      assert s1.Peek(13) == 0x17b;
      assert s1.Peek(14) == 0x180;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17c4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s534(s5, gas - 1)
      else
        ExecuteFromCFGNode_s533(s5, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 327
    * Starting at 0x17c0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xf73

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xf73;
      assert s1.Peek(13) == 0x17b;
      assert s1.Peek(14) == 0x180;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 534
    * Segment Id for this node is: 328
    * Starting at 0x17c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xf73

    requires s0.stack[12] == 0x17b

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xf73;
      assert s1.Peek(12) == 0x17b;
      assert s1.Peek(13) == 0x180;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s535(s3, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 188
    * Starting at 0xec3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xf73

    requires s0.stack[10] == 0x17b

    requires s0.stack[11] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf73;
      assert s1.Peek(10) == 0x17b;
      assert s1.Peek(11) == 0x180;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s6, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 203
    * Starting at 0xf73
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x17b

    requires s0.stack[8] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x17b;
      assert s1.Peek(8) == 0x180;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s537(s10, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 36
    * Starting at 0x17b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x180;
      var s2 := Push2(s1, 0x03e1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s538(s3, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 89
    * Starting at 0x3e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x03ec);
      var s5 := Push2(s4, 0x0723);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s6, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 134
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x3ec

    requires s0.stack[6] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3ec;
      assert s1.Peek(6) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s7, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 90
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x03f9);
      var s5 := Dup6(s4);
      var s6 := Dup3(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x08f6);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s541(s9, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 144
    * Starting at 0x8f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3f9

    requires s0.stack[9] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3f9;
      assert s1.Peek(9) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0902);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0618);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s7, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 126
    * Starting at 0x618
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x618 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x902

    requires s0.stack[7] == 0x3f9

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x902;
      assert s1.Peek(7) == 0x3f9;
      assert s1.Peek(13) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x902;
      assert s11.Peek(10) == 0x3f9;
      assert s11.Peek(16) == 0x180;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x902;
      assert s21.Peek(10) == 0x3f9;
      assert s21.Peek(16) == 0x180;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x902;
      assert s31.Peek(10) == 0x3f9;
      assert s31.Peek(16) == 0x180;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s543(s41, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 127
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x902

    requires s0.stack[8] == 0x3f9

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x902;
      assert s1.Peek(8) == 0x3f9;
      assert s1.Peek(14) == 0x180;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s544(s4, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 145
    * Starting at 0x902
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x902 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x3f9

    requires s0.stack[11] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3f9;
      assert s1.Peek(11) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x097c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s585(s8, gas - 1)
      else
        ExecuteFromCFGNode_s545(s8, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 146
    * Starting at 0x92c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3f9

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x3f9;
      assert s1.Peek(11) == 0x180;
      var s2 := Dup2(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x096e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s555(s6, gas - 1)
      else
        ExecuteFromCFGNode_s546(s6, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 147
    * Starting at 0x934
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x934 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3f9

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x3f9;
      assert s1.Peek(11) == 0x180;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0965);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1244);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s11, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 264
    * Starting at 0x1244
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x965

    requires s0.stack[6] == 0x3f9

    requires s0.stack[12] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x965;
      assert s1.Peek(6) == 0x3f9;
      assert s1.Peek(12) == 0x180;
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
      assert s11.Peek(4) == 0x965;
      assert s11.Peek(9) == 0x3f9;
      assert s11.Peek(15) == 0x180;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x125d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1079);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s548(s18, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 227
    * Starting at 0x1079
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1079 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x125d

    requires s0.stack[4] == 0x965

    requires s0.stack[9] == 0x3f9

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x125d;
      assert s1.Peek(4) == 0x965;
      assert s1.Peek(9) == 0x3f9;
      assert s1.Peek(15) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1086);
      var s4 := Push1(s3, 0x1d);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s549(s7, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1086

    requires s0.stack[5] == 0x125d

    requires s0.stack[8] == 0x965

    requires s0.stack[13] == 0x3f9

    requires s0.stack[19] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1086;
      assert s1.Peek(5) == 0x125d;
      assert s1.Peek(8) == 0x965;
      assert s1.Peek(13) == 0x3f9;
      assert s1.Peek(19) == 0x180;
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
      assert s11.Peek(0) == 0x1086;
      assert s11.Peek(6) == 0x125d;
      assert s11.Peek(9) == 0x965;
      assert s11.Peek(14) == 0x3f9;
      assert s11.Peek(20) == 0x180;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s550(s15, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 228
    * Starting at 0x1086
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1086 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x125d

    requires s0.stack[6] == 0x965

    requires s0.stack[11] == 0x3f9

    requires s0.stack[17] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x125d;
      assert s1.Peek(6) == 0x965;
      assert s1.Peek(11) == 0x3f9;
      assert s1.Peek(17) == 0x180;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1091);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x15e2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s551(s7, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 314
    * Starting at 0x15e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x1091

    requires s0.stack[4] == 0x125d

    requires s0.stack[7] == 0x965

    requires s0.stack[12] == 0x3f9

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1091;
      assert s1.Peek(4) == 0x125d;
      assert s1.Peek(7) == 0x965;
      assert s1.Peek(12) == 0x3f9;
      assert s1.Peek(18) == 0x180;
      var s2 := Push32(s1, 0x45524332303a20696e73756666696369656e7420616c6c6f77616e6365000000);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s552(s8, gas - 1)
  }

  /** Node 552
    * Segment Id for this node is: 229
    * Starting at 0x1091
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1091 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x125d

    requires s0.stack[5] == 0x965

    requires s0.stack[10] == 0x3f9

    requires s0.stack[16] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x125d;
      assert s1.Peek(5) == 0x965;
      assert s1.Peek(10) == 0x3f9;
      assert s1.Peek(16) == 0x180;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s553(s10, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 265
    * Starting at 0x125d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x965

    requires s0.stack[8] == 0x3f9

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x965;
      assert s1.Peek(8) == 0x3f9;
      assert s1.Peek(14) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s7, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 148
    * Starting at 0x965
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x965 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x3f9

    requires s0.stack[11] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3f9;
      assert s1.Peek(11) == 0x180;
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

  /** Node 555
    * Segment Id for this node is: 149
    * Starting at 0x96e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3f9

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3f9;
      assert s1.Peek(10) == 0x180;
      var s2 := Push2(s1, 0x097b);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x072b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s556(s9, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 135
    * Starting at 0x72b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x97b

    requires s0.stack[8] == 0x3f9

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x97b;
      assert s1.Peek(8) == 0x3f9;
      assert s1.Peek(14) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x079b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s566(s11, gas - 1)
      else
        ExecuteFromCFGNode_s557(s11, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 136
    * Starting at 0x761
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x761 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x97b

    requires s0.stack[8] == 0x3f9

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x97b;
      assert s1.Peek(9) == 0x3f9;
      assert s1.Peek(15) == 0x180;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0792);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12c4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s558(s11, gas - 1)
  }

  /** Node 558
    * Segment Id for this node is: 272
    * Starting at 0x12c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x792

    requires s0.stack[5] == 0x97b

    requires s0.stack[10] == 0x3f9

    requires s0.stack[16] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x792;
      assert s1.Peek(5) == 0x97b;
      assert s1.Peek(10) == 0x3f9;
      assert s1.Peek(16) == 0x180;
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
      assert s11.Peek(4) == 0x792;
      assert s11.Peek(8) == 0x97b;
      assert s11.Peek(13) == 0x3f9;
      assert s11.Peek(19) == 0x180;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12dd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1105);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s559(s18, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 239
    * Starting at 0x1105
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x12dd

    requires s0.stack[4] == 0x792

    requires s0.stack[8] == 0x97b

    requires s0.stack[13] == 0x3f9

    requires s0.stack[19] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12dd;
      assert s1.Peek(4) == 0x792;
      assert s1.Peek(8) == 0x97b;
      assert s1.Peek(13) == 0x3f9;
      assert s1.Peek(19) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1112);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s560(s7, gas - 1)
  }

  /** Node 560
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x1112

    requires s0.stack[5] == 0x12dd

    requires s0.stack[8] == 0x792

    requires s0.stack[12] == 0x97b

    requires s0.stack[17] == 0x3f9

    requires s0.stack[23] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1112;
      assert s1.Peek(5) == 0x12dd;
      assert s1.Peek(8) == 0x792;
      assert s1.Peek(12) == 0x97b;
      assert s1.Peek(17) == 0x3f9;
      assert s1.Peek(23) == 0x180;
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
      assert s11.Peek(0) == 0x1112;
      assert s11.Peek(6) == 0x12dd;
      assert s11.Peek(9) == 0x792;
      assert s11.Peek(13) == 0x97b;
      assert s11.Peek(18) == 0x3f9;
      assert s11.Peek(24) == 0x180;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s561(s15, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 240
    * Starting at 0x1112
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1112 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x12dd

    requires s0.stack[6] == 0x792

    requires s0.stack[10] == 0x97b

    requires s0.stack[15] == 0x3f9

    requires s0.stack[21] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12dd;
      assert s1.Peek(6) == 0x792;
      assert s1.Peek(10) == 0x97b;
      assert s1.Peek(15) == 0x3f9;
      assert s1.Peek(21) == 0x180;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x111d);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x16d2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s562(s7, gas - 1)
  }

  /** Node 562
    * Segment Id for this node is: 318
    * Starting at 0x16d2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x111d

    requires s0.stack[4] == 0x12dd

    requires s0.stack[7] == 0x792

    requires s0.stack[11] == 0x97b

    requires s0.stack[16] == 0x3f9

    requires s0.stack[22] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x111d;
      assert s1.Peek(4) == 0x12dd;
      assert s1.Peek(7) == 0x792;
      assert s1.Peek(11) == 0x97b;
      assert s1.Peek(16) == 0x3f9;
      assert s1.Peek(22) == 0x180;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x111d;
      assert s11.Peek(4) == 0x12dd;
      assert s11.Peek(7) == 0x792;
      assert s11.Peek(11) == 0x97b;
      assert s11.Peek(16) == 0x3f9;
      assert s11.Peek(22) == 0x180;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s563(s13, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 241
    * Starting at 0x111d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x12dd

    requires s0.stack[5] == 0x792

    requires s0.stack[9] == 0x97b

    requires s0.stack[14] == 0x3f9

    requires s0.stack[20] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12dd;
      assert s1.Peek(5) == 0x792;
      assert s1.Peek(9) == 0x97b;
      assert s1.Peek(14) == 0x3f9;
      assert s1.Peek(20) == 0x180;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s10, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 273
    * Starting at 0x12dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x792

    requires s0.stack[7] == 0x97b

    requires s0.stack[12] == 0x3f9

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x792;
      assert s1.Peek(7) == 0x97b;
      assert s1.Peek(12) == 0x3f9;
      assert s1.Peek(18) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s565(s7, gas - 1)
  }

  /** Node 565
    * Segment Id for this node is: 137
    * Starting at 0x792
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x97b

    requires s0.stack[9] == 0x3f9

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x97b;
      assert s1.Peek(9) == 0x3f9;
      assert s1.Peek(15) == 0x180;
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

  /** Node 566
    * Segment Id for this node is: 138
    * Starting at 0x79b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x97b

    requires s0.stack[8] == 0x3f9

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x97b;
      assert s1.Peek(8) == 0x3f9;
      assert s1.Peek(14) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x080b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s576(s11, gas - 1)
      else
        ExecuteFromCFGNode_s567(s11, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 139
    * Starting at 0x7d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x97b

    requires s0.stack[8] == 0x3f9

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x97b;
      assert s1.Peek(9) == 0x3f9;
      assert s1.Peek(15) == 0x180;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0802);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1224);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s568(s11, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 262
    * Starting at 0x1224
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1224 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x802

    requires s0.stack[5] == 0x97b

    requires s0.stack[10] == 0x3f9

    requires s0.stack[16] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x802;
      assert s1.Peek(5) == 0x97b;
      assert s1.Peek(10) == 0x3f9;
      assert s1.Peek(16) == 0x180;
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
      assert s11.Peek(4) == 0x802;
      assert s11.Peek(8) == 0x97b;
      assert s11.Peek(13) == 0x3f9;
      assert s11.Peek(19) == 0x180;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x123d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1056);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s18, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 224
    * Starting at 0x1056
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1056 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x123d

    requires s0.stack[4] == 0x802

    requires s0.stack[8] == 0x97b

    requires s0.stack[13] == 0x3f9

    requires s0.stack[19] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x123d;
      assert s1.Peek(4) == 0x802;
      assert s1.Peek(8) == 0x97b;
      assert s1.Peek(13) == 0x3f9;
      assert s1.Peek(19) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1063);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s570(s7, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x1063

    requires s0.stack[5] == 0x123d

    requires s0.stack[8] == 0x802

    requires s0.stack[12] == 0x97b

    requires s0.stack[17] == 0x3f9

    requires s0.stack[23] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(5) == 0x123d;
      assert s1.Peek(8) == 0x802;
      assert s1.Peek(12) == 0x97b;
      assert s1.Peek(17) == 0x3f9;
      assert s1.Peek(23) == 0x180;
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
      assert s11.Peek(0) == 0x1063;
      assert s11.Peek(6) == 0x123d;
      assert s11.Peek(9) == 0x802;
      assert s11.Peek(13) == 0x97b;
      assert s11.Peek(18) == 0x3f9;
      assert s11.Peek(24) == 0x180;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s571(s15, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 225
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x123d

    requires s0.stack[6] == 0x802

    requires s0.stack[10] == 0x97b

    requires s0.stack[15] == 0x3f9

    requires s0.stack[21] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x123d;
      assert s1.Peek(6) == 0x802;
      assert s1.Peek(10) == 0x97b;
      assert s1.Peek(15) == 0x3f9;
      assert s1.Peek(21) == 0x180;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x106e);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1593);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s572(s7, gas - 1)
  }

  /** Node 572
    * Segment Id for this node is: 313
    * Starting at 0x1593
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x106e

    requires s0.stack[4] == 0x123d

    requires s0.stack[7] == 0x802

    requires s0.stack[11] == 0x97b

    requires s0.stack[16] == 0x3f9

    requires s0.stack[22] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106e;
      assert s1.Peek(4) == 0x123d;
      assert s1.Peek(7) == 0x802;
      assert s1.Peek(11) == 0x97b;
      assert s1.Peek(16) == 0x3f9;
      assert s1.Peek(22) == 0x180;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x106e;
      assert s11.Peek(4) == 0x123d;
      assert s11.Peek(7) == 0x802;
      assert s11.Peek(11) == 0x97b;
      assert s11.Peek(16) == 0x3f9;
      assert s11.Peek(22) == 0x180;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s573(s13, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 226
    * Starting at 0x106e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x123d

    requires s0.stack[5] == 0x802

    requires s0.stack[9] == 0x97b

    requires s0.stack[14] == 0x3f9

    requires s0.stack[20] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x123d;
      assert s1.Peek(5) == 0x802;
      assert s1.Peek(9) == 0x97b;
      assert s1.Peek(14) == 0x3f9;
      assert s1.Peek(20) == 0x180;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s574(s10, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 263
    * Starting at 0x123d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x802

    requires s0.stack[7] == 0x97b

    requires s0.stack[12] == 0x3f9

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x802;
      assert s1.Peek(7) == 0x97b;
      assert s1.Peek(12) == 0x3f9;
      assert s1.Peek(18) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s575(s7, gas - 1)
  }

  /** Node 575
    * Segment Id for this node is: 140
    * Starting at 0x802
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x802 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x97b

    requires s0.stack[9] == 0x3f9

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x97b;
      assert s1.Peek(9) == 0x3f9;
      assert s1.Peek(15) == 0x180;
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

  /** Node 576
    * Segment Id for this node is: 141
    * Starting at 0x80b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x97b

    requires s0.stack[8] == 0x3f9

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x97b;
      assert s1.Peek(8) == 0x3f9;
      assert s1.Peek(14) == 0x180;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x97b;
      assert s11.Peek(11) == 0x3f9;
      assert s11.Peek(17) == 0x180;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x97b;
      assert s21.Peek(11) == 0x3f9;
      assert s21.Peek(17) == 0x180;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x97b;
      assert s31.Peek(11) == 0x3f9;
      assert s31.Peek(17) == 0x180;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s577(s41, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 142
    * Starting at 0x88d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x97b

    requires s0.stack[8] == 0x3f9

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x97b;
      assert s1.Peek(9) == 0x3f9;
      assert s1.Peek(15) == 0x180;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08e9);
      assert s11.Peek(0) == 0x8e9;
      assert s11.Peek(9) == 0x97b;
      assert s11.Peek(14) == 0x3f9;
      assert s11.Peek(20) == 0x180;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x1324);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s578(s15, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x8e9

    requires s0.stack[9] == 0x97b

    requires s0.stack[14] == 0x3f9

    requires s0.stack[20] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e9;
      assert s1.Peek(9) == 0x97b;
      assert s1.Peek(14) == 0x3f9;
      assert s1.Peek(20) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0x8e9;
      assert s11.Peek(12) == 0x97b;
      assert s11.Peek(17) == 0x3f9;
      assert s11.Peek(23) == 0x180;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s579(s14, gas - 1)
  }

  /** Node 579
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0x8e9

    requires s0.stack[13] == 0x97b

    requires s0.stack[18] == 0x3f9

    requires s0.stack[24] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0x8e9;
      assert s1.Peek(13) == 0x97b;
      assert s1.Peek(18) == 0x3f9;
      assert s1.Peek(24) == 0x180;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s580(s5, gas - 1)
  }

  /** Node 580
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0x8e9

    requires s0.stack[15] == 0x97b

    requires s0.stack[20] == 0x3f9

    requires s0.stack[26] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0x8e9;
      assert s1.Peek(15) == 0x97b;
      assert s1.Peek(20) == 0x3f9;
      assert s1.Peek(26) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s581(s9, gas - 1)
  }

  /** Node 581
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0x8e9

    requires s0.stack[14] == 0x97b

    requires s0.stack[19] == 0x3f9

    requires s0.stack[25] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0x8e9;
      assert s1.Peek(14) == 0x97b;
      assert s1.Peek(19) == 0x3f9;
      assert s1.Peek(25) == 0x180;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s582(s6, gas - 1)
  }

  /** Node 582
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x8e9

    requires s0.stack[10] == 0x97b

    requires s0.stack[15] == 0x3f9

    requires s0.stack[21] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8e9;
      assert s1.Peek(10) == 0x97b;
      assert s1.Peek(15) == 0x3f9;
      assert s1.Peek(21) == 0x180;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s583(s6, gas - 1)
  }

  /** Node 583
    * Segment Id for this node is: 143
    * Starting at 0x8e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s583(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x97b

    requires s0.stack[12] == 0x3f9

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x97b;
      assert s1.Peek(12) == 0x3f9;
      assert s1.Peek(18) == 0x180;
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
      assert s11.Peek(0) == 0x97b;
      assert s11.Peek(5) == 0x3f9;
      assert s11.Peek(11) == 0x180;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s584(s12, gas - 1)
  }

  /** Node 584
    * Segment Id for this node is: 150
    * Starting at 0x97b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s584(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3f9

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s585(s1, gas - 1)
  }

  /** Node 585
    * Segment Id for this node is: 151
    * Starting at 0x97c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s585(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3f9

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3f9;
      assert s1.Peek(10) == 0x180;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s586(s6, gas - 1)
  }

  /** Node 586
    * Segment Id for this node is: 91
    * Starting at 0x3f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s586(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x180;
      var s2 := Push2(s1, 0x0404);
      var s3 := Dup6(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x0982);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s587(s7, gas - 1)
  }

  /** Node 587
    * Segment Id for this node is: 152
    * Starting at 0x982
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s587(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x982 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x404

    requires s0.stack[9] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x404;
      assert s1.Peek(9) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x09f2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s597(s11, gas - 1)
      else
        ExecuteFromCFGNode_s588(s11, gas - 1)
  }

  /** Node 588
    * Segment Id for this node is: 153
    * Starting at 0x9b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s588(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x404

    requires s0.stack[9] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x404;
      assert s1.Peek(10) == 0x180;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x09e9);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12a4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s589(s11, gas - 1)
  }

  /** Node 589
    * Segment Id for this node is: 270
    * Starting at 0x12a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s589(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x9e9

    requires s0.stack[5] == 0x404

    requires s0.stack[11] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9e9;
      assert s1.Peek(5) == 0x404;
      assert s1.Peek(11) == 0x180;
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
      assert s11.Peek(4) == 0x9e9;
      assert s11.Peek(8) == 0x404;
      assert s11.Peek(14) == 0x180;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12bd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10e2);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s590(s18, gas - 1)
  }

  /** Node 590
    * Segment Id for this node is: 236
    * Starting at 0x10e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s590(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x12bd

    requires s0.stack[4] == 0x9e9

    requires s0.stack[8] == 0x404

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12bd;
      assert s1.Peek(4) == 0x9e9;
      assert s1.Peek(8) == 0x404;
      assert s1.Peek(14) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10ef);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s591(s7, gas - 1)
  }

  /** Node 591
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s591(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x10ef

    requires s0.stack[5] == 0x12bd

    requires s0.stack[8] == 0x9e9

    requires s0.stack[12] == 0x404

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ef;
      assert s1.Peek(5) == 0x12bd;
      assert s1.Peek(8) == 0x9e9;
      assert s1.Peek(12) == 0x404;
      assert s1.Peek(18) == 0x180;
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
      assert s11.Peek(0) == 0x10ef;
      assert s11.Peek(6) == 0x12bd;
      assert s11.Peek(9) == 0x9e9;
      assert s11.Peek(13) == 0x404;
      assert s11.Peek(19) == 0x180;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s592(s15, gas - 1)
  }

  /** Node 592
    * Segment Id for this node is: 237
    * Starting at 0x10ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s592(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x12bd

    requires s0.stack[6] == 0x9e9

    requires s0.stack[10] == 0x404

    requires s0.stack[16] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12bd;
      assert s1.Peek(6) == 0x9e9;
      assert s1.Peek(10) == 0x404;
      assert s1.Peek(16) == 0x180;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10fa);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1683);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s593(s7, gas - 1)
  }

  /** Node 593
    * Segment Id for this node is: 317
    * Starting at 0x1683
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s593(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x10fa

    requires s0.stack[4] == 0x12bd

    requires s0.stack[7] == 0x9e9

    requires s0.stack[11] == 0x404

    requires s0.stack[17] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10fa;
      assert s1.Peek(4) == 0x12bd;
      assert s1.Peek(7) == 0x9e9;
      assert s1.Peek(11) == 0x404;
      assert s1.Peek(17) == 0x180;
      var s2 := Push32(s1, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x10fa;
      assert s11.Peek(4) == 0x12bd;
      assert s11.Peek(7) == 0x9e9;
      assert s11.Peek(11) == 0x404;
      assert s11.Peek(17) == 0x180;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s594(s13, gas - 1)
  }

  /** Node 594
    * Segment Id for this node is: 238
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s594(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x12bd

    requires s0.stack[5] == 0x9e9

    requires s0.stack[9] == 0x404

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12bd;
      assert s1.Peek(5) == 0x9e9;
      assert s1.Peek(9) == 0x404;
      assert s1.Peek(15) == 0x180;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s595(s10, gas - 1)
  }

  /** Node 595
    * Segment Id for this node is: 271
    * Starting at 0x12bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s595(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x9e9

    requires s0.stack[7] == 0x404

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9e9;
      assert s1.Peek(7) == 0x404;
      assert s1.Peek(13) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s596(s7, gas - 1)
  }

  /** Node 596
    * Segment Id for this node is: 154
    * Starting at 0x9e9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s596(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x404

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x404;
      assert s1.Peek(10) == 0x180;
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

  /** Node 597
    * Segment Id for this node is: 155
    * Starting at 0x9f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s597(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x404

    requires s0.stack[9] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x404;
      assert s1.Peek(9) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0a62);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s607(s11, gas - 1)
      else
        ExecuteFromCFGNode_s598(s11, gas - 1)
  }

  /** Node 598
    * Segment Id for this node is: 156
    * Starting at 0xa28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s598(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x404

    requires s0.stack[9] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x404;
      assert s1.Peek(10) == 0x180;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a59);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x11e4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s599(s11, gas - 1)
  }

  /** Node 599
    * Segment Id for this node is: 258
    * Starting at 0x11e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s599(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xa59

    requires s0.stack[5] == 0x404

    requires s0.stack[11] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa59;
      assert s1.Peek(5) == 0x404;
      assert s1.Peek(11) == 0x180;
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
      assert s11.Peek(4) == 0xa59;
      assert s11.Peek(8) == 0x404;
      assert s11.Peek(14) == 0x180;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x11fd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1010);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s600(s18, gas - 1)
  }

  /** Node 600
    * Segment Id for this node is: 218
    * Starting at 0x1010
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s600(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1010 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x11fd

    requires s0.stack[4] == 0xa59

    requires s0.stack[8] == 0x404

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11fd;
      assert s1.Peek(4) == 0xa59;
      assert s1.Peek(8) == 0x404;
      assert s1.Peek(14) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x101d);
      var s4 := Push1(s3, 0x23);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s601(s7, gas - 1)
  }

  /** Node 601
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s601(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x101d

    requires s0.stack[5] == 0x11fd

    requires s0.stack[8] == 0xa59

    requires s0.stack[12] == 0x404

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x101d;
      assert s1.Peek(5) == 0x11fd;
      assert s1.Peek(8) == 0xa59;
      assert s1.Peek(12) == 0x404;
      assert s1.Peek(18) == 0x180;
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
      assert s11.Peek(0) == 0x101d;
      assert s11.Peek(6) == 0x11fd;
      assert s11.Peek(9) == 0xa59;
      assert s11.Peek(13) == 0x404;
      assert s11.Peek(19) == 0x180;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s602(s15, gas - 1)
  }

  /** Node 602
    * Segment Id for this node is: 219
    * Starting at 0x101d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s602(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x11fd

    requires s0.stack[6] == 0xa59

    requires s0.stack[10] == 0x404

    requires s0.stack[16] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11fd;
      assert s1.Peek(6) == 0xa59;
      assert s1.Peek(10) == 0x404;
      assert s1.Peek(16) == 0x180;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1028);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x14f5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s603(s7, gas - 1)
  }

  /** Node 603
    * Segment Id for this node is: 311
    * Starting at 0x14f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s603(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x1028

    requires s0.stack[4] == 0x11fd

    requires s0.stack[7] == 0xa59

    requires s0.stack[11] == 0x404

    requires s0.stack[17] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1028;
      assert s1.Peek(4) == 0x11fd;
      assert s1.Peek(7) == 0xa59;
      assert s1.Peek(11) == 0x404;
      assert s1.Peek(17) == 0x180;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1028;
      assert s11.Peek(4) == 0x11fd;
      assert s11.Peek(7) == 0xa59;
      assert s11.Peek(11) == 0x404;
      assert s11.Peek(17) == 0x180;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s604(s13, gas - 1)
  }

  /** Node 604
    * Segment Id for this node is: 220
    * Starting at 0x1028
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s604(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1028 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x11fd

    requires s0.stack[5] == 0xa59

    requires s0.stack[9] == 0x404

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11fd;
      assert s1.Peek(5) == 0xa59;
      assert s1.Peek(9) == 0x404;
      assert s1.Peek(15) == 0x180;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s605(s10, gas - 1)
  }

  /** Node 605
    * Segment Id for this node is: 259
    * Starting at 0x11fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s605(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa59

    requires s0.stack[7] == 0x404

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa59;
      assert s1.Peek(7) == 0x404;
      assert s1.Peek(13) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s606(s7, gas - 1)
  }

  /** Node 606
    * Segment Id for this node is: 157
    * Starting at 0xa59
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s606(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x404

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x404;
      assert s1.Peek(10) == 0x180;
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

  /** Node 607
    * Segment Id for this node is: 158
    * Starting at 0xa62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s607(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x404

    requires s0.stack[9] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x404;
      assert s1.Peek(9) == 0x180;
      var s2 := Push2(s1, 0x0a6d);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e95);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s608(s7, gas - 1)
  }

  /** Node 608
    * Segment Id for this node is: 183
    * Starting at 0xe95
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s608(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe95 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa6d

    requires s0.stack[7] == 0x404

    requires s0.stack[13] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa6d;
      assert s1.Peek(7) == 0x404;
      assert s1.Peek(13) == 0x180;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s609(s5, gas - 1)
  }

  /** Node 609
    * Segment Id for this node is: 159
    * Starting at 0xa6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s609(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x404

    requires s0.stack[9] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x404;
      assert s1.Peek(9) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x404;
      assert s11.Peek(12) == 0x180;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x404;
      assert s21.Peek(11) == 0x180;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0af3);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s619(s29, gas - 1)
      else
        ExecuteFromCFGNode_s610(s29, gas - 1)
  }

  /** Node 610
    * Segment Id for this node is: 160
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s610(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x404

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x404;
      assert s1.Peek(11) == 0x180;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0aea);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1264);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s611(s11, gas - 1)
  }

  /** Node 611
    * Segment Id for this node is: 266
    * Starting at 0x1264
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s611(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1264 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xaea

    requires s0.stack[6] == 0x404

    requires s0.stack[12] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaea;
      assert s1.Peek(6) == 0x404;
      assert s1.Peek(12) == 0x180;
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
      assert s11.Peek(4) == 0xaea;
      assert s11.Peek(9) == 0x404;
      assert s11.Peek(15) == 0x180;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x127d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x109c);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s612(s18, gas - 1)
  }

  /** Node 612
    * Segment Id for this node is: 230
    * Starting at 0x109c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s612(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x127d

    requires s0.stack[4] == 0xaea

    requires s0.stack[9] == 0x404

    requires s0.stack[15] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x127d;
      assert s1.Peek(4) == 0xaea;
      assert s1.Peek(9) == 0x404;
      assert s1.Peek(15) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10a9);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s613(s7, gas - 1)
  }

  /** Node 613
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s613(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x10a9

    requires s0.stack[5] == 0x127d

    requires s0.stack[8] == 0xaea

    requires s0.stack[13] == 0x404

    requires s0.stack[19] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10a9;
      assert s1.Peek(5) == 0x127d;
      assert s1.Peek(8) == 0xaea;
      assert s1.Peek(13) == 0x404;
      assert s1.Peek(19) == 0x180;
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
      assert s11.Peek(0) == 0x10a9;
      assert s11.Peek(6) == 0x127d;
      assert s11.Peek(9) == 0xaea;
      assert s11.Peek(14) == 0x404;
      assert s11.Peek(20) == 0x180;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s614(s15, gas - 1)
  }

  /** Node 614
    * Segment Id for this node is: 231
    * Starting at 0x10a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s614(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x127d

    requires s0.stack[6] == 0xaea

    requires s0.stack[11] == 0x404

    requires s0.stack[17] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x127d;
      assert s1.Peek(6) == 0xaea;
      assert s1.Peek(11) == 0x404;
      assert s1.Peek(17) == 0x180;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10b4);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x160b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s615(s7, gas - 1)
  }

  /** Node 615
    * Segment Id for this node is: 315
    * Starting at 0x160b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s615(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x10b4

    requires s0.stack[4] == 0x127d

    requires s0.stack[7] == 0xaea

    requires s0.stack[12] == 0x404

    requires s0.stack[18] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10b4;
      assert s1.Peek(4) == 0x127d;
      assert s1.Peek(7) == 0xaea;
      assert s1.Peek(12) == 0x404;
      assert s1.Peek(18) == 0x180;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x616c616e63650000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x10b4;
      assert s11.Peek(4) == 0x127d;
      assert s11.Peek(7) == 0xaea;
      assert s11.Peek(12) == 0x404;
      assert s11.Peek(18) == 0x180;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s616(s13, gas - 1)
  }

  /** Node 616
    * Segment Id for this node is: 232
    * Starting at 0x10b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s616(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x127d

    requires s0.stack[5] == 0xaea

    requires s0.stack[10] == 0x404

    requires s0.stack[16] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x127d;
      assert s1.Peek(5) == 0xaea;
      assert s1.Peek(10) == 0x404;
      assert s1.Peek(16) == 0x180;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s617(s10, gas - 1)
  }

  /** Node 617
    * Segment Id for this node is: 267
    * Starting at 0x127d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s617(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaea

    requires s0.stack[8] == 0x404

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaea;
      assert s1.Peek(8) == 0x404;
      assert s1.Peek(14) == 0x180;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s618(s7, gas - 1)
  }

  /** Node 618
    * Segment Id for this node is: 161
    * Starting at 0xaea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s618(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x404

    requires s0.stack[11] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x404;
      assert s1.Peek(11) == 0x180;
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

  /** Node 619
    * Segment Id for this node is: 162
    * Starting at 0xaf3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s619(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x404

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x404;
      assert s1.Peek(10) == 0x180;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x404;
      assert s11.Peek(14) == 0x180;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(7) == 0x404;
      assert s21.Peek(13) == 0x180;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Dup2(s26);
      var s28 := Push1(s27, 0x00);
      var s29 := Dup1(s28);
      var s30 := Dup6(s29);
      var s31 := Push20(s30, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s31.Peek(9) == 0x404;
      assert s31.Peek(15) == 0x180;
      var s32 := And(s31);
      var s33 := Push20(s32, 0xffffffffffffffffffffffffffffffffffffffff);
      var s34 := And(s33);
      var s35 := Dup2(s34);
      var s36 := MStore(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Add(s37);
      var s39 := Swap1(s38);
      var s40 := Dup2(s39);
      var s41 := MStore(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s620(s41, gas - 1)
  }

  /** Node 620
    * Segment Id for this node is: 163
    * Starting at 0xb72
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s620(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x404

    requires s0.stack[12] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x404;
      assert s1.Peek(13) == 0x180;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Keccak256(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup3(s5);
      var s7 := Dup3(s6);
      var s8 := SLoad(s7);
      var s9 := Add(s8);
      var s10 := Swap3(s9);
      var s11 := Pop(s10);
      assert s11.Peek(7) == 0x404;
      assert s11.Peek(13) == 0x180;
      var s12 := Pop(s11);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := SStore(s14);
      var s16 := Pop(s15);
      var s17 := Dup3(s16);
      var s18 := Push20(s17, 0xffffffffffffffffffffffffffffffffffffffff);
      var s19 := And(s18);
      var s20 := Dup5(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(7) == 0x404;
      assert s21.Peek(13) == 0x180;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x0be1);
      var s28 := Swap2(s27);
      var s29 := Swap1(s28);
      var s30 := Push2(s29, 0x1324);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s621(s31, gas - 1)
  }

  /** Node 621
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s621(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xbe1

    requires s0.stack[10] == 0x404

    requires s0.stack[16] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbe1;
      assert s1.Peek(10) == 0x404;
      assert s1.Peek(16) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0xbe1;
      assert s11.Peek(13) == 0x404;
      assert s11.Peek(19) == 0x180;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s622(s14, gas - 1)
  }

  /** Node 622
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s622(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0xbe1

    requires s0.stack[14] == 0x404

    requires s0.stack[20] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0xbe1;
      assert s1.Peek(14) == 0x404;
      assert s1.Peek(20) == 0x180;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s623(s5, gas - 1)
  }

  /** Node 623
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s623(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0xbe1

    requires s0.stack[16] == 0x404

    requires s0.stack[22] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0xbe1;
      assert s1.Peek(16) == 0x404;
      assert s1.Peek(22) == 0x180;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s624(s9, gas - 1)
  }

  /** Node 624
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s624(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0xbe1

    requires s0.stack[15] == 0x404

    requires s0.stack[21] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0xbe1;
      assert s1.Peek(15) == 0x404;
      assert s1.Peek(21) == 0x180;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s625(s6, gas - 1)
  }

  /** Node 625
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s625(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xbe1

    requires s0.stack[11] == 0x404

    requires s0.stack[17] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbe1;
      assert s1.Peek(11) == 0x404;
      assert s1.Peek(17) == 0x180;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s626(s6, gas - 1)
  }

  /** Node 626
    * Segment Id for this node is: 164
    * Starting at 0xbe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s626(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x404

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x404;
      assert s1.Peek(14) == 0x180;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x0bf4);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(2) == 0xbf4;
      assert s11.Peek(7) == 0x404;
      assert s11.Peek(13) == 0x180;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e9a);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s627(s14, gas - 1)
  }

  /** Node 627
    * Segment Id for this node is: 184
    * Starting at 0xe9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s627(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xbf4

    requires s0.stack[8] == 0x404

    requires s0.stack[14] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbf4;
      assert s1.Peek(8) == 0x404;
      assert s1.Peek(14) == 0x180;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s628(s5, gas - 1)
  }

  /** Node 628
    * Segment Id for this node is: 165
    * Starting at 0xbf4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s628(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x404

    requires s0.stack[10] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x404;
      assert s1.Peek(10) == 0x180;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s629(s6, gas - 1)
  }

  /** Node 629
    * Segment Id for this node is: 92
    * Starting at 0x404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s629(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x180;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap4(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s630(s11, gas - 1)
  }

  /** Node 630
    * Segment Id for this node is: 37
    * Starting at 0x180
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s630(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x180 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x018d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11a7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s631(s8, gas - 1)
  }

  /** Node 631
    * Segment Id for this node is: 254
    * Starting at 0x11a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s631(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x18d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x18d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x11bc);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x11bc;
      assert s11.Peek(5) == 0x18d;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0fc8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s632(s14, gas - 1)
  }

  /** Node 632
    * Segment Id for this node is: 211
    * Starting at 0xfc8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s632(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11bc

    requires s0.stack[6] == 0x18d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11bc;
      assert s1.Peek(6) == 0x18d;
      var s2 := Push2(s1, 0x0fd1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13de);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s633(s5, gas - 1)
  }

  /** Node 633
    * Segment Id for this node is: 292
    * Starting at 0x13de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s633(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfd1

    requires s0.stack[4] == 0x11bc

    requires s0.stack[8] == 0x18d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfd1;
      assert s1.Peek(4) == 0x11bc;
      assert s1.Peek(8) == 0x18d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s634(s11, gas - 1)
  }

  /** Node 634
    * Segment Id for this node is: 212
    * Starting at 0xfd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s634(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11bc

    requires s0.stack[7] == 0x18d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11bc;
      assert s1.Peek(7) == 0x18d;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s635(s6, gas - 1)
  }

  /** Node 635
    * Segment Id for this node is: 255
    * Starting at 0x11bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s635(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x18d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x18d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s636(s6, gas - 1)
  }

  /** Node 636
    * Segment Id for this node is: 38
    * Starting at 0x18d
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s636(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18d as nat
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

  /** Node 637
    * Segment Id for this node is: 21
    * Starting at 0xd3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s637(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s711(s6, gas - 1)
      else
        ExecuteFromCFGNode_s638(s6, gas - 1)
  }

  /** Node 638
    * Segment Id for this node is: 22
    * Starting at 0xdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s638(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s649(s5, gas - 1)
      else
        ExecuteFromCFGNode_s639(s5, gas - 1)
  }

  /** Node 639
    * Segment Id for this node is: 23
    * Starting at 0xea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s639(s0: EState, gas: nat): (s': EState)
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
      var s4 := Push2(s3, 0x0148);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s640(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 640
    * Segment Id for this node is: 32
    * Starting at 0x148
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s640(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0150);
      var s3 := Push2(s2, 0x03d7);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s641(s4, gas - 1)
  }

  /** Node 641
    * Segment Id for this node is: 88
    * Starting at 0x3d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s641(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x150

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x150;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s642(s8, gas - 1)
  }

  /** Node 642
    * Segment Id for this node is: 33
    * Starting at 0x150
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s642(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x150 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x015d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1324);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s643(s8, gas - 1)
  }

  /** Node 643
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s643(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x15d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0x15d;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s644(s14, gas - 1)
  }

  /** Node 644
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s644(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0x15d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0x15d;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s645(s5, gas - 1)
  }

  /** Node 645
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s645(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0x15d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0x15d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s646(s9, gas - 1)
  }

  /** Node 646
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s646(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0x15d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0x15d;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s647(s6, gas - 1)
  }

  /** Node 647
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s647(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x15d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x15d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s648(s6, gas - 1)
  }

  /** Node 648
    * Segment Id for this node is: 34
    * Starting at 0x15d
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s648(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15d as nat
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

  /** Node 649
    * Segment Id for this node is: 28
    * Starting at 0x118
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s649(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0132);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x012d);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x12d;
      assert s11.Peek(3) == 0x132;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f7d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s650(s14, gas - 1)
  }

  /** Node 650
    * Segment Id for this node is: 204
    * Starting at 0xf7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s650(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x12d

    requires s0.stack[3] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12d;
      assert s1.Peek(3) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f90);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s652(s11, gas - 1)
      else
        ExecuteFromCFGNode_s651(s11, gas - 1)
  }

  /** Node 651
    * Segment Id for this node is: 205
    * Starting at 0xf8c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s651(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x12d

    requires s0.stack[5] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x12d;
      assert s1.Peek(6) == 0x132;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 652
    * Segment Id for this node is: 206
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s652(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x12d

    requires s0.stack[5] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x12d;
      assert s1.Peek(5) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f9e);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e9f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s653(s9, gas - 1)
  }

  /** Node 653
    * Segment Id for this node is: 185
    * Starting at 0xe9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s653(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf9e

    requires s0.stack[8] == 0x12d

    requires s0.stack[9] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9e;
      assert s1.Peek(8) == 0x12d;
      assert s1.Peek(9) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0eae);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1799);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s654(s10, gas - 1)
  }

  /** Node 654
    * Segment Id for this node is: 321
    * Starting at 0x1799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s654(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x12d

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x12d;
      assert s1.Peek(12) == 0x132;
      var s2 := Push2(s1, 0x17a2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13cc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s655(s5, gas - 1)
  }

  /** Node 655
    * Segment Id for this node is: 290
    * Starting at 0x13cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s655(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17a2

    requires s0.stack[3] == 0xeae

    requires s0.stack[7] == 0xf9e

    requires s0.stack[13] == 0x12d

    requires s0.stack[14] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a2;
      assert s1.Peek(3) == 0xeae;
      assert s1.Peek(7) == 0xf9e;
      assert s1.Peek(13) == 0x12d;
      assert s1.Peek(14) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13d7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x13ea);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s656(s6, gas - 1)
  }

  /** Node 656
    * Segment Id for this node is: 293
    * Starting at 0x13ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s656(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x13d7

    requires s0.stack[4] == 0x17a2

    requires s0.stack[6] == 0xeae

    requires s0.stack[10] == 0xf9e

    requires s0.stack[16] == 0x12d

    requires s0.stack[17] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13d7;
      assert s1.Peek(4) == 0x17a2;
      assert s1.Peek(6) == 0xeae;
      assert s1.Peek(10) == 0xf9e;
      assert s1.Peek(16) == 0x12d;
      assert s1.Peek(17) == 0x132;
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
      ExecuteFromCFGNode_s657(s11, gas - 1)
  }

  /** Node 657
    * Segment Id for this node is: 291
    * Starting at 0x13d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s657(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x17a2

    requires s0.stack[5] == 0xeae

    requires s0.stack[9] == 0xf9e

    requires s0.stack[15] == 0x12d

    requires s0.stack[16] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17a2;
      assert s1.Peek(5) == 0xeae;
      assert s1.Peek(9) == 0xf9e;
      assert s1.Peek(15) == 0x12d;
      assert s1.Peek(16) == 0x132;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s658(s7, gas - 1)
  }

  /** Node 658
    * Segment Id for this node is: 322
    * Starting at 0x17a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s658(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xeae

    requires s0.stack[6] == 0xf9e

    requires s0.stack[12] == 0x12d

    requires s0.stack[13] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x12d;
      assert s1.Peek(13) == 0x132;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17ad);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s660(s5, gas - 1)
      else
        ExecuteFromCFGNode_s659(s5, gas - 1)
  }

  /** Node 659
    * Segment Id for this node is: 323
    * Starting at 0x17a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s659(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x12d

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xeae;
      assert s1.Peek(6) == 0xf9e;
      assert s1.Peek(12) == 0x12d;
      assert s1.Peek(13) == 0x132;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 660
    * Segment Id for this node is: 324
    * Starting at 0x17ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s660(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xeae

    requires s0.stack[5] == 0xf9e

    requires s0.stack[11] == 0x12d

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeae;
      assert s1.Peek(5) == 0xf9e;
      assert s1.Peek(11) == 0x12d;
      assert s1.Peek(12) == 0x132;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s661(s3, gas - 1)
  }

  /** Node 661
    * Segment Id for this node is: 186
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s661(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf9e

    requires s0.stack[9] == 0x12d

    requires s0.stack[10] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9e;
      assert s1.Peek(9) == 0x12d;
      assert s1.Peek(10) == 0x132;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s662(s6, gas - 1)
  }

  /** Node 662
    * Segment Id for this node is: 207
    * Starting at 0xf9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s662(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x12d

    requires s0.stack[7] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x12d;
      assert s1.Peek(7) == 0x132;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0faf);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0eb4);
      assert s11.Peek(0) == 0xeb4;
      assert s11.Peek(3) == 0xfaf;
      assert s11.Peek(9) == 0x12d;
      assert s11.Peek(10) == 0x132;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s663(s12, gas - 1)
  }

  /** Node 663
    * Segment Id for this node is: 187
    * Starting at 0xeb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s663(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xfaf

    requires s0.stack[8] == 0x12d

    requires s0.stack[9] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaf;
      assert s1.Peek(8) == 0x12d;
      assert s1.Peek(9) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ec3);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x17b0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s664(s10, gas - 1)
  }

  /** Node 664
    * Segment Id for this node is: 325
    * Starting at 0x17b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s664(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x12d

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x12d;
      assert s1.Peek(12) == 0x132;
      var s2 := Push2(s1, 0x17b9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s665(s5, gas - 1)
  }

  /** Node 665
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s665(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x17b9

    requires s0.stack[3] == 0xec3

    requires s0.stack[7] == 0xfaf

    requires s0.stack[13] == 0x12d

    requires s0.stack[14] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17b9;
      assert s1.Peek(3) == 0xec3;
      assert s1.Peek(7) == 0xfaf;
      assert s1.Peek(13) == 0x12d;
      assert s1.Peek(14) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s666(s9, gas - 1)
  }

  /** Node 666
    * Segment Id for this node is: 326
    * Starting at 0x17b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s666(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xec3

    requires s0.stack[6] == 0xfaf

    requires s0.stack[12] == 0x12d

    requires s0.stack[13] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x12d;
      assert s1.Peek(13) == 0x132;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x17c4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s668(s5, gas - 1)
      else
        ExecuteFromCFGNode_s667(s5, gas - 1)
  }

  /** Node 667
    * Segment Id for this node is: 327
    * Starting at 0x17c0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s667(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x12d

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xec3;
      assert s1.Peek(6) == 0xfaf;
      assert s1.Peek(12) == 0x12d;
      assert s1.Peek(13) == 0x132;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 668
    * Segment Id for this node is: 328
    * Starting at 0x17c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s668(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xec3

    requires s0.stack[5] == 0xfaf

    requires s0.stack[11] == 0x12d

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec3;
      assert s1.Peek(5) == 0xfaf;
      assert s1.Peek(11) == 0x12d;
      assert s1.Peek(12) == 0x132;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s669(s3, gas - 1)
  }

  /** Node 669
    * Segment Id for this node is: 188
    * Starting at 0xec3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s669(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xfaf

    requires s0.stack[9] == 0x12d

    requires s0.stack[10] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfaf;
      assert s1.Peek(9) == 0x12d;
      assert s1.Peek(10) == 0x132;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s670(s6, gas - 1)
  }

  /** Node 670
    * Segment Id for this node is: 208
    * Starting at 0xfaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s670(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x12d

    requires s0.stack[7] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x12d;
      assert s1.Peek(7) == 0x132;
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
      ExecuteFromCFGNode_s671(s10, gas - 1)
  }

  /** Node 671
    * Segment Id for this node is: 29
    * Starting at 0x12d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s671(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x132;
      var s2 := Push2(s1, 0x03b4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s672(s3, gas - 1)
  }

  /** Node 672
    * Segment Id for this node is: 85
    * Starting at 0x3b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s672(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Push2(s4, 0x0723);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s673(s6, gas - 1)
  }

  /** Node 673
    * Segment Id for this node is: 134
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s673(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x3bf

    requires s0.stack[5] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bf;
      assert s1.Peek(5) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s674(s7, gas - 1)
  }

  /** Node 674
    * Segment Id for this node is: 86
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s674(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x132;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x03cc);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x072b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s675(s9, gas - 1)
  }

  /** Node 675
    * Segment Id for this node is: 135
    * Starting at 0x72b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s675(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3cc

    requires s0.stack[8] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3cc;
      assert s1.Peek(8) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x079b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s685(s11, gas - 1)
      else
        ExecuteFromCFGNode_s676(s11, gas - 1)
  }

  /** Node 676
    * Segment Id for this node is: 136
    * Starting at 0x761
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s676(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x761 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3cc

    requires s0.stack[8] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3cc;
      assert s1.Peek(9) == 0x132;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0792);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12c4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s677(s11, gas - 1)
  }

  /** Node 677
    * Segment Id for this node is: 272
    * Starting at 0x12c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s677(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x792

    requires s0.stack[5] == 0x3cc

    requires s0.stack[10] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x792;
      assert s1.Peek(5) == 0x3cc;
      assert s1.Peek(10) == 0x132;
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
      assert s11.Peek(4) == 0x792;
      assert s11.Peek(8) == 0x3cc;
      assert s11.Peek(13) == 0x132;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12dd);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1105);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s678(s18, gas - 1)
  }

  /** Node 678
    * Segment Id for this node is: 239
    * Starting at 0x1105
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s678(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x12dd

    requires s0.stack[4] == 0x792

    requires s0.stack[8] == 0x3cc

    requires s0.stack[13] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12dd;
      assert s1.Peek(4) == 0x792;
      assert s1.Peek(8) == 0x3cc;
      assert s1.Peek(13) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1112);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s679(s7, gas - 1)
  }

  /** Node 679
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s679(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1112

    requires s0.stack[5] == 0x12dd

    requires s0.stack[8] == 0x792

    requires s0.stack[12] == 0x3cc

    requires s0.stack[17] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1112;
      assert s1.Peek(5) == 0x12dd;
      assert s1.Peek(8) == 0x792;
      assert s1.Peek(12) == 0x3cc;
      assert s1.Peek(17) == 0x132;
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
      assert s11.Peek(0) == 0x1112;
      assert s11.Peek(6) == 0x12dd;
      assert s11.Peek(9) == 0x792;
      assert s11.Peek(13) == 0x3cc;
      assert s11.Peek(18) == 0x132;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s680(s15, gas - 1)
  }

  /** Node 680
    * Segment Id for this node is: 240
    * Starting at 0x1112
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s680(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1112 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x12dd

    requires s0.stack[6] == 0x792

    requires s0.stack[10] == 0x3cc

    requires s0.stack[15] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12dd;
      assert s1.Peek(6) == 0x792;
      assert s1.Peek(10) == 0x3cc;
      assert s1.Peek(15) == 0x132;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x111d);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x16d2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s681(s7, gas - 1)
  }

  /** Node 681
    * Segment Id for this node is: 318
    * Starting at 0x16d2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s681(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x111d

    requires s0.stack[4] == 0x12dd

    requires s0.stack[7] == 0x792

    requires s0.stack[11] == 0x3cc

    requires s0.stack[16] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x111d;
      assert s1.Peek(4) == 0x12dd;
      assert s1.Peek(7) == 0x792;
      assert s1.Peek(11) == 0x3cc;
      assert s1.Peek(16) == 0x132;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x111d;
      assert s11.Peek(4) == 0x12dd;
      assert s11.Peek(7) == 0x792;
      assert s11.Peek(11) == 0x3cc;
      assert s11.Peek(16) == 0x132;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s682(s13, gas - 1)
  }

  /** Node 682
    * Segment Id for this node is: 241
    * Starting at 0x111d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s682(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x12dd

    requires s0.stack[5] == 0x792

    requires s0.stack[9] == 0x3cc

    requires s0.stack[14] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12dd;
      assert s1.Peek(5) == 0x792;
      assert s1.Peek(9) == 0x3cc;
      assert s1.Peek(14) == 0x132;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s683(s10, gas - 1)
  }

  /** Node 683
    * Segment Id for this node is: 273
    * Starting at 0x12dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s683(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x792

    requires s0.stack[7] == 0x3cc

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x792;
      assert s1.Peek(7) == 0x3cc;
      assert s1.Peek(12) == 0x132;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s684(s7, gas - 1)
  }

  /** Node 684
    * Segment Id for this node is: 137
    * Starting at 0x792
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s684(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x3cc

    requires s0.stack[9] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3cc;
      assert s1.Peek(9) == 0x132;
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

  /** Node 685
    * Segment Id for this node is: 138
    * Starting at 0x79b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s685(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3cc

    requires s0.stack[8] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3cc;
      assert s1.Peek(8) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x080b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s695(s11, gas - 1)
      else
        ExecuteFromCFGNode_s686(s11, gas - 1)
  }

  /** Node 686
    * Segment Id for this node is: 139
    * Starting at 0x7d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s686(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3cc

    requires s0.stack[8] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3cc;
      assert s1.Peek(9) == 0x132;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0802);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1224);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s687(s11, gas - 1)
  }

  /** Node 687
    * Segment Id for this node is: 262
    * Starting at 0x1224
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s687(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1224 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x802

    requires s0.stack[5] == 0x3cc

    requires s0.stack[10] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x802;
      assert s1.Peek(5) == 0x3cc;
      assert s1.Peek(10) == 0x132;
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
      assert s11.Peek(4) == 0x802;
      assert s11.Peek(8) == 0x3cc;
      assert s11.Peek(13) == 0x132;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x123d);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1056);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s688(s18, gas - 1)
  }

  /** Node 688
    * Segment Id for this node is: 224
    * Starting at 0x1056
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s688(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1056 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x123d

    requires s0.stack[4] == 0x802

    requires s0.stack[8] == 0x3cc

    requires s0.stack[13] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x123d;
      assert s1.Peek(4) == 0x802;
      assert s1.Peek(8) == 0x3cc;
      assert s1.Peek(13) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1063);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1365);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s689(s7, gas - 1)
  }

  /** Node 689
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s689(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1063

    requires s0.stack[5] == 0x123d

    requires s0.stack[8] == 0x802

    requires s0.stack[12] == 0x3cc

    requires s0.stack[17] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(5) == 0x123d;
      assert s1.Peek(8) == 0x802;
      assert s1.Peek(12) == 0x3cc;
      assert s1.Peek(17) == 0x132;
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
      assert s11.Peek(0) == 0x1063;
      assert s11.Peek(6) == 0x123d;
      assert s11.Peek(9) == 0x802;
      assert s11.Peek(13) == 0x3cc;
      assert s11.Peek(18) == 0x132;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s690(s15, gas - 1)
  }

  /** Node 690
    * Segment Id for this node is: 225
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s690(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x123d

    requires s0.stack[6] == 0x802

    requires s0.stack[10] == 0x3cc

    requires s0.stack[15] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x123d;
      assert s1.Peek(6) == 0x802;
      assert s1.Peek(10) == 0x3cc;
      assert s1.Peek(15) == 0x132;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x106e);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1593);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s691(s7, gas - 1)
  }

  /** Node 691
    * Segment Id for this node is: 313
    * Starting at 0x1593
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s691(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x106e

    requires s0.stack[4] == 0x123d

    requires s0.stack[7] == 0x802

    requires s0.stack[11] == 0x3cc

    requires s0.stack[16] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106e;
      assert s1.Peek(4) == 0x123d;
      assert s1.Peek(7) == 0x802;
      assert s1.Peek(11) == 0x3cc;
      assert s1.Peek(16) == 0x132;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x106e;
      assert s11.Peek(4) == 0x123d;
      assert s11.Peek(7) == 0x802;
      assert s11.Peek(11) == 0x3cc;
      assert s11.Peek(16) == 0x132;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s692(s13, gas - 1)
  }

  /** Node 692
    * Segment Id for this node is: 226
    * Starting at 0x106e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s692(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x123d

    requires s0.stack[5] == 0x802

    requires s0.stack[9] == 0x3cc

    requires s0.stack[14] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x123d;
      assert s1.Peek(5) == 0x802;
      assert s1.Peek(9) == 0x3cc;
      assert s1.Peek(14) == 0x132;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s693(s10, gas - 1)
  }

  /** Node 693
    * Segment Id for this node is: 263
    * Starting at 0x123d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s693(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x802

    requires s0.stack[7] == 0x3cc

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x802;
      assert s1.Peek(7) == 0x3cc;
      assert s1.Peek(12) == 0x132;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s694(s7, gas - 1)
  }

  /** Node 694
    * Segment Id for this node is: 140
    * Starting at 0x802
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s694(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x802 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x3cc

    requires s0.stack[9] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3cc;
      assert s1.Peek(9) == 0x132;
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

  /** Node 695
    * Segment Id for this node is: 141
    * Starting at 0x80b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s695(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3cc

    requires s0.stack[8] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3cc;
      assert s1.Peek(8) == 0x132;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x3cc;
      assert s11.Peek(11) == 0x132;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x3cc;
      assert s21.Peek(11) == 0x132;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x3cc;
      assert s31.Peek(11) == 0x132;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s696(s41, gas - 1)
  }

  /** Node 696
    * Segment Id for this node is: 142
    * Starting at 0x88d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s696(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3cc

    requires s0.stack[8] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x3cc;
      assert s1.Peek(9) == 0x132;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08e9);
      assert s11.Peek(0) == 0x8e9;
      assert s11.Peek(9) == 0x3cc;
      assert s11.Peek(14) == 0x132;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x1324);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s697(s15, gas - 1)
  }

  /** Node 697
    * Segment Id for this node is: 278
    * Starting at 0x1324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s697(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x8e9

    requires s0.stack[9] == 0x3cc

    requires s0.stack[14] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e9;
      assert s1.Peek(9) == 0x3cc;
      assert s1.Peek(14) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1339);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1339;
      assert s11.Peek(5) == 0x8e9;
      assert s11.Peek(12) == 0x3cc;
      assert s11.Peek(17) == 0x132;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x116e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s698(s14, gas - 1)
  }

  /** Node 698
    * Segment Id for this node is: 248
    * Starting at 0x116e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s698(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1339

    requires s0.stack[6] == 0x8e9

    requires s0.stack[13] == 0x3cc

    requires s0.stack[18] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1339;
      assert s1.Peek(6) == 0x8e9;
      assert s1.Peek(13) == 0x3cc;
      assert s1.Peek(18) == 0x132;
      var s2 := Push2(s1, 0x1177);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x140a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s699(s5, gas - 1)
  }

  /** Node 699
    * Segment Id for this node is: 294
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s699(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x1177

    requires s0.stack[4] == 0x1339

    requires s0.stack[8] == 0x8e9

    requires s0.stack[15] == 0x3cc

    requires s0.stack[20] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1177;
      assert s1.Peek(4) == 0x1339;
      assert s1.Peek(8) == 0x8e9;
      assert s1.Peek(15) == 0x3cc;
      assert s1.Peek(20) == 0x132;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s700(s9, gas - 1)
  }

  /** Node 700
    * Segment Id for this node is: 249
    * Starting at 0x1177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s700(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x1339

    requires s0.stack[7] == 0x8e9

    requires s0.stack[14] == 0x3cc

    requires s0.stack[19] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1339;
      assert s1.Peek(7) == 0x8e9;
      assert s1.Peek(14) == 0x3cc;
      assert s1.Peek(19) == 0x132;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s701(s6, gas - 1)
  }

  /** Node 701
    * Segment Id for this node is: 279
    * Starting at 0x1339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s701(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x8e9

    requires s0.stack[10] == 0x3cc

    requires s0.stack[15] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8e9;
      assert s1.Peek(10) == 0x3cc;
      assert s1.Peek(15) == 0x132;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s702(s6, gas - 1)
  }

  /** Node 702
    * Segment Id for this node is: 143
    * Starting at 0x8e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s702(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x3cc

    requires s0.stack[12] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3cc;
      assert s1.Peek(12) == 0x132;
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
      assert s11.Peek(0) == 0x3cc;
      assert s11.Peek(5) == 0x132;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s703(s12, gas - 1)
  }

  /** Node 703
    * Segment Id for this node is: 87
    * Starting at 0x3cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s703(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x132

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x132;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s704(s10, gas - 1)
  }

  /** Node 704
    * Segment Id for this node is: 30
    * Starting at 0x132
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s704(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x013f);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11a7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s705(s8, gas - 1)
  }

  /** Node 705
    * Segment Id for this node is: 254
    * Starting at 0x11a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s705(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x11bc);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x11bc;
      assert s11.Peek(5) == 0x13f;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0fc8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s706(s14, gas - 1)
  }

  /** Node 706
    * Segment Id for this node is: 211
    * Starting at 0xfc8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s706(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11bc

    requires s0.stack[6] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11bc;
      assert s1.Peek(6) == 0x13f;
      var s2 := Push2(s1, 0x0fd1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x13de);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s707(s5, gas - 1)
  }

  /** Node 707
    * Segment Id for this node is: 292
    * Starting at 0x13de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s707(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfd1

    requires s0.stack[4] == 0x11bc

    requires s0.stack[8] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfd1;
      assert s1.Peek(4) == 0x11bc;
      assert s1.Peek(8) == 0x13f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s708(s11, gas - 1)
  }

  /** Node 708
    * Segment Id for this node is: 212
    * Starting at 0xfd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s708(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11bc

    requires s0.stack[7] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11bc;
      assert s1.Peek(7) == 0x13f;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s709(s6, gas - 1)
  }

  /** Node 709
    * Segment Id for this node is: 255
    * Starting at 0x11bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s709(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s710(s6, gas - 1)
  }

  /** Node 710
    * Segment Id for this node is: 31
    * Starting at 0x13f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s710(s0: EState, gas: nat): (s': EState)
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
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 711
    * Segment Id for this node is: 25
    * Starting at 0xfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s711(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push2(s2, 0x0322);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s712(s4, gas - 1)
  }

  /** Node 712
    * Segment Id for this node is: 76
    * Starting at 0x322
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s712(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x322 as nat
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
      var s6 := Push2(s5, 0x0331);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x1454);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s713(s9, gas - 1)
  }

  /** Node 713
    * Segment Id for this node is: 302
    * Starting at 0x1454
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s713(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1454 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x331

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x331;
      assert s1.Peek(4) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x331;
      assert s11.Peek(7) == 0x102;
      var s12 := Push2(s11, 0x146c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s715(s13, gas - 1)
      else
        ExecuteFromCFGNode_s714(s13, gas - 1)
  }

  /** Node 714
    * Segment Id for this node is: 303
    * Starting at 0x1466
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s714(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1466 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x331

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(7) == 0x102;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s715(s5, gas - 1)
  }

  /** Node 715
    * Segment Id for this node is: 304
    * Starting at 0x146c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s715(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x331

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(6) == 0x102;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1480);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s718(s9, gas - 1)
      else
        ExecuteFromCFGNode_s716(s9, gas - 1)
  }

  /** Node 716
    * Segment Id for this node is: 305
    * Starting at 0x1478
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s716(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1478 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x331

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x147f);
      assert s1.Peek(0) == 0x147f;
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(7) == 0x102;
      var s2 := Push2(s1, 0x14b5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s717(s3, gas - 1)
  }

  /** Node 717
    * Segment Id for this node is: 309
    * Starting at 0x14b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s717(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x147f

    requires s0.stack[4] == 0x331

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x147f;
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(7) == 0x102;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 718
    * Segment Id for this node is: 307
    * Starting at 0x1480
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s718(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1480 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x331

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(6) == 0x102;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s719(s6, gas - 1)
  }

  /** Node 719
    * Segment Id for this node is: 77
    * Starting at 0x331
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s719(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
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
      var s31 := Push2(s30, 0x035d);
      assert s31.Peek(0) == 0x35d;
      assert s31.Peek(8) == 0x102;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x1454);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s720(s34, gas - 1)
  }

  /** Node 720
    * Segment Id for this node is: 302
    * Starting at 0x1454
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s720(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1454 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x35d

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x35d;
      assert s1.Peek(8) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x35d;
      assert s11.Peek(11) == 0x102;
      var s12 := Push2(s11, 0x146c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s722(s13, gas - 1)
      else
        ExecuteFromCFGNode_s721(s13, gas - 1)
  }

  /** Node 721
    * Segment Id for this node is: 303
    * Starting at 0x1466
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s721(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1466 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x35d

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x35d;
      assert s1.Peek(11) == 0x102;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s722(s5, gas - 1)
  }

  /** Node 722
    * Segment Id for this node is: 304
    * Starting at 0x146c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s722(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x35d

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35d;
      assert s1.Peek(10) == 0x102;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1480);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s725(s9, gas - 1)
      else
        ExecuteFromCFGNode_s723(s9, gas - 1)
  }

  /** Node 723
    * Segment Id for this node is: 305
    * Starting at 0x1478
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s723(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1478 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x35d

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x147f);
      assert s1.Peek(0) == 0x147f;
      assert s1.Peek(4) == 0x35d;
      assert s1.Peek(11) == 0x102;
      var s2 := Push2(s1, 0x14b5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s724(s3, gas - 1)
  }

  /** Node 724
    * Segment Id for this node is: 309
    * Starting at 0x14b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s724(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x147f

    requires s0.stack[4] == 0x35d

    requires s0.stack[11] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x147f;
      assert s1.Peek(4) == 0x35d;
      assert s1.Peek(11) == 0x102;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 725
    * Segment Id for this node is: 307
    * Starting at 0x1480
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s725(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1480 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x35d

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35d;
      assert s1.Peek(10) == 0x102;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s726(s6, gas - 1)
  }

  /** Node 726
    * Segment Id for this node is: 78
    * Starting at 0x35d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s726(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35d as nat
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
      var s4 := Push2(s3, 0x03aa);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s729(s5, gas - 1)
      else
        ExecuteFromCFGNode_s727(s5, gas - 1)
  }

  /** Node 727
    * Segment Id for this node is: 79
    * Starting at 0x364
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s727(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
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
      var s4 := Push2(s3, 0x037f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s748(s5, gas - 1)
      else
        ExecuteFromCFGNode_s728(s5, gas - 1)
  }

  /** Node 728
    * Segment Id for this node is: 80
    * Starting at 0x36c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s728(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36c as nat
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
      var s13 := Push2(s12, 0x03aa);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s729(s14, gas - 1)
  }

  /** Node 729
    * Segment Id for this node is: 84
    * Starting at 0x3aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s729(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3aa as nat
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
      ExecuteFromCFGNode_s730(s10, gas - 1)
  }

  /** Node 730
    * Segment Id for this node is: 26
    * Starting at 0x102
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s730(s0: EState, gas: nat): (s': EState)
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
      var s7 := Push2(s6, 0x11c2);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s731(s8, gas - 1)
  }

  /** Node 731
    * Segment Id for this node is: 256
    * Starting at 0x11c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s731(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c2 as nat
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
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x10f;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x11dc);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0fd7);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s732(s19, gas - 1)
  }

  /** Node 732
    * Segment Id for this node is: 213
    * Starting at 0xfd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s732(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11dc

    requires s0.stack[6] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11dc;
      assert s1.Peek(6) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0fe2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x135a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s733(s6, gas - 1)
  }

  /** Node 733
    * Segment Id for this node is: 282
    * Starting at 0x135a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s733(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xfe2

    requires s0.stack[5] == 0x11dc

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfe2;
      assert s1.Peek(5) == 0x11dc;
      assert s1.Peek(9) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s734(s10, gas - 1)
  }

  /** Node 734
    * Segment Id for this node is: 214
    * Starting at 0xfe2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s734(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x11dc

    requires s0.stack[8] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x11dc;
      assert s1.Peek(8) == 0x10f;
      var s2 := Push2(s1, 0x0fec);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x1365);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s735(s6, gas - 1)
  }

  /** Node 735
    * Segment Id for this node is: 283
    * Starting at 0x1365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s735(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xfec

    requires s0.stack[7] == 0x11dc

    requires s0.stack[11] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfec;
      assert s1.Peek(7) == 0x11dc;
      assert s1.Peek(11) == 0x10f;
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
      assert s11.Peek(0) == 0xfec;
      assert s11.Peek(8) == 0x11dc;
      assert s11.Peek(12) == 0x10f;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s736(s15, gas - 1)
  }

  /** Node 736
    * Segment Id for this node is: 215
    * Starting at 0xfec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s736(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x11dc

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11dc;
      assert s1.Peek(9) == 0x10f;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0ffc);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x1421);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s737(s11, gas - 1)
  }

  /** Node 737
    * Segment Id for this node is: 296
    * Starting at 0x1421
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s737(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1421 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xffc

    requires s0.stack[8] == 0x11dc

    requires s0.stack[12] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xffc;
      assert s1.Peek(8) == 0x11dc;
      assert s1.Peek(12) == 0x10f;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s738(s2, gas - 1)
  }

  /** Node 738
    * Segment Id for this node is: 297
    * Starting at 0x1424
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s738(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1424 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xffc;
      assert s1.Peek(9) == 0x11dc;
      assert s1.Peek(13) == 0x10f;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x143f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s740(s7, gas - 1)
      else
        ExecuteFromCFGNode_s739(s7, gas - 1)
  }

  /** Node 739
    * Segment Id for this node is: 298
    * Starting at 0x142d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s739(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x142d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xffc;
      assert s1.Peek(10) == 0x11dc;
      assert s1.Peek(14) == 0x10f;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0xffc;
      assert s11.Peek(10) == 0x11dc;
      assert s11.Peek(14) == 0x10f;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x1424);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s738(s15, gas - 1)
  }

  /** Node 740
    * Segment Id for this node is: 299
    * Starting at 0x143f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s740(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xffc;
      assert s1.Peek(9) == 0x11dc;
      assert s1.Peek(13) == 0x10f;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x144e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s742(s7, gas - 1)
      else
        ExecuteFromCFGNode_s741(s7, gas - 1)
  }

  /** Node 741
    * Segment Id for this node is: 300
    * Starting at 0x1448
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s741(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1448 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xffc;
      assert s1.Peek(10) == 0x11dc;
      assert s1.Peek(14) == 0x10f;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s742(s5, gas - 1)
  }

  /** Node 742
    * Segment Id for this node is: 301
    * Starting at 0x144e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s742(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x144e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xffc

    requires s0.stack[9] == 0x11dc

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xffc;
      assert s1.Peek(9) == 0x11dc;
      assert s1.Peek(13) == 0x10f;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s743(s6, gas - 1)
  }

  /** Node 743
    * Segment Id for this node is: 216
    * Starting at 0xffc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s743(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x11dc

    requires s0.stack[8] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x11dc;
      assert s1.Peek(8) == 0x10f;
      var s2 := Push2(s1, 0x1005);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x14e4);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s744(s5, gas - 1)
  }

  /** Node 744
    * Segment Id for this node is: 310
    * Starting at 0x14e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s744(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1005

    requires s0.stack[6] == 0x11dc

    requires s0.stack[10] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1005;
      assert s1.Peek(6) == 0x11dc;
      assert s1.Peek(10) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1005;
      assert s11.Peek(7) == 0x11dc;
      assert s11.Peek(11) == 0x10f;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s745(s14, gas - 1)
  }

  /** Node 745
    * Segment Id for this node is: 217
    * Starting at 0x1005
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s745(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1005 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x11dc

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11dc;
      assert s1.Peek(9) == 0x10f;
      var s2 := Dup5(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s746(s11, gas - 1)
  }

  /** Node 746
    * Segment Id for this node is: 257
    * Starting at 0x11dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s746(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s747(s8, gas - 1)
  }

  /** Node 747
    * Segment Id for this node is: 27
    * Starting at 0x10f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s747(s0: EState, gas: nat): (s': EState)
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

  /** Node 748
    * Segment Id for this node is: 81
    * Starting at 0x37f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s748(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37f as nat
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
      ExecuteFromCFGNode_s749(s11, gas - 1)
  }

  /** Node 749
    * Segment Id for this node is: 82
    * Starting at 0x38d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s749(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38d as nat
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
      var s15 := Push2(s14, 0x038d);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s749(s16, gas - 1)
      else
        ExecuteFromCFGNode_s750(s16, gas - 1)
  }

  /** Node 750
    * Segment Id for this node is: 83
    * Starting at 0x3a1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s750(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a1 as nat
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
      ExecuteFromCFGNode_s729(s8, gas - 1)
  }

  /** Node 751
    * Segment Id for this node is: 24
    * Starting at 0xf5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s751(s0: EState, gas: nat): (s': EState)
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
