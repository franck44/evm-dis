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
      var s7 := Push2(s6, 0x000f);
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
      var s1 := Push0(s0);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0xf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf as nat
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
      var s6 := Push2(s5, 0x003f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s7, gas - 1)
      else
        ExecuteFromCFGNode_s3(s7, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup1(s4);
      var s6 := Push4(s5, 0x028cff6a);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0043);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s9, gas - 1)
      else
        ExecuteFromCFGNode_s4(s9, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x29
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x252dba42);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0058);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x6cc301e3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0082);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 7
    * Segment Id for this node is: 14
    * Starting at 0x82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00a4);
      var s3 := Push2(s2, 0x0090);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x02b4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s8(s7, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 46
    * Starting at 0x2b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x90

    requires s0.stack[3] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x90;
      assert s1.Peek(3) == 0xa4;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02c4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s10, gas - 1)
      else
        ExecuteFromCFGNode_s9(s10, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 47
    * Starting at 0x2c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x90

    requires s0.stack[4] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x90;
      assert s1.Peek(5) == 0xa4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 10
    * Segment Id for this node is: 48
    * Starting at 0x2c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x90

    requires s0.stack[4] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x90;
      assert s1.Peek(4) == 0xa4;
      var s2 := Push2(s1, 0x02cd);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0299);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 43
    * Starting at 0x299
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x2cd

    requires s0.stack[5] == 0x90

    requires s0.stack[6] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2cd;
      assert s1.Peek(5) == 0x90;
      assert s1.Peek(6) == 0xa4;
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
      assert s11.Peek(4) == 0x2cd;
      assert s11.Peek(8) == 0x90;
      assert s11.Peek(9) == 0xa4;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x02af);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s14, gas - 1)
      else
        ExecuteFromCFGNode_s12(s14, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 44
    * Starting at 0x2ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x2cd

    requires s0.stack[6] == 0x90

    requires s0.stack[7] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x2cd;
      assert s1.Peek(7) == 0x90;
      assert s1.Peek(8) == 0xa4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 13
    * Segment Id for this node is: 45
    * Starting at 0x2af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x2cd

    requires s0.stack[6] == 0x90

    requires s0.stack[7] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2cd;
      assert s1.Peek(6) == 0x90;
      assert s1.Peek(7) == 0xa4;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s5, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 49
    * Starting at 0x2cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x90

    requires s0.stack[5] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x90;
      assert s1.Peek(5) == 0xa4;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s7, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 15
    * Starting at 0x90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa4;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup2(s3);
      var s5 := Swap1(s4);
      var s6 := MStore(s5);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xa4;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0xff);
      var s15 := And(s14);
      var s16 := Dup2(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s17, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 16
    * Starting at 0xa4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa4;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0079);
      assert s11.Peek(0) == 0x79;
      assert s11.Peek(2) == 0xa4;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s12, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 13
    * Starting at 0x79
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xa4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa4;
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

  /** Node 18
    * Segment Id for this node is: 10
    * Starting at 0x58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x006b);
      var s3 := Push2(s2, 0x0066);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0342);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s7, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 57
    * Starting at 0x342
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x66

    requires s0.stack[3] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x66;
      assert s1.Peek(3) == 0x6b;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0353);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s11, gas - 1)
      else
        ExecuteFromCFGNode_s20(s11, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 58
    * Starting at 0x350
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x350 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x66

    requires s0.stack[5] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x66;
      assert s1.Peek(6) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 21
    * Segment Id for this node is: 59
    * Starting at 0x353
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x353 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x66

    requires s0.stack[5] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x66;
      assert s1.Peek(5) == 0x6b;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x036a);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s10, gas - 1)
      else
        ExecuteFromCFGNode_s22(s10, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 60
    * Starting at 0x367
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x367 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x66

    requires s0.stack[7] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x66;
      assert s1.Peek(8) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 23
    * Segment Id for this node is: 61
    * Starting at 0x36a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x66

    requires s0.stack[7] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x66;
      assert s1.Peek(7) == 0x6b;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup6(s6);
      var s8 := Push1(s7, 0x1f);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := SLt(s10);
      assert s11.Peek(7) == 0x66;
      assert s11.Peek(8) == 0x6b;
      var s12 := Push2(s11, 0x037d);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s13, gas - 1)
      else
        ExecuteFromCFGNode_s24(s13, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 62
    * Starting at 0x37a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x66

    requires s0.stack[7] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x66;
      assert s1.Peek(8) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 25
    * Segment Id for this node is: 63
    * Starting at 0x37d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x66

    requires s0.stack[7] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x66;
      assert s1.Peek(7) == 0x6b;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x038f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s9, gas - 1)
      else
        ExecuteFromCFGNode_s26(s9, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 64
    * Starting at 0x388
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x388 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x66

    requires s0.stack[8] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x038f);
      assert s1.Peek(0) == 0x38f;
      assert s1.Peek(8) == 0x66;
      assert s1.Peek(9) == 0x6b;
      var s2 := Push2(s1, 0x02d4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s3, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 50
    * Starting at 0x2d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x38f

    requires s0.stack[8] == 0x66

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x38f;
      assert s1.Peek(8) == 0x66;
      assert s1.Peek(9) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x38f;
      assert s11.Peek(10) == 0x66;
      assert s11.Peek(11) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 28
    * Segment Id for this node is: 65
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x66

    requires s0.stack[8] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x66;
      assert s1.Peek(8) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Push2(s4, 0x039e);
      var s6 := Dup6(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0311);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s10, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 54
    * Starting at 0x311
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x311 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x39e

    requires s0.stack[10] == 0x66

    requires s0.stack[11] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x39e;
      assert s1.Peek(10) == 0x66;
      assert s1.Peek(11) == 0x6b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x39e;
      assert s11.Peek(12) == 0x66;
      assert s11.Peek(13) == 0x6b;
      var s12 := Push8(s11, 0xffffffffffffffff);
      var s13 := Dup2(s12);
      var s14 := Gt(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Lt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x033a);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s32(s21, gas - 1)
      else
        ExecuteFromCFGNode_s30(s21, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 55
    * Starting at 0x333
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x333 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x39e

    requires s0.stack[12] == 0x66

    requires s0.stack[13] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x033a);
      assert s1.Peek(0) == 0x33a;
      assert s1.Peek(4) == 0x39e;
      assert s1.Peek(13) == 0x66;
      assert s1.Peek(14) == 0x6b;
      var s2 := Push2(s1, 0x02d4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s3, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 50
    * Starting at 0x2d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x33a

    requires s0.stack[4] == 0x39e

    requires s0.stack[13] == 0x66

    requires s0.stack[14] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x33a;
      assert s1.Peek(4) == 0x39e;
      assert s1.Peek(13) == 0x66;
      assert s1.Peek(14) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x33a;
      assert s11.Peek(6) == 0x39e;
      assert s11.Peek(15) == 0x66;
      assert s11.Peek(16) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 32
    * Segment Id for this node is: 56
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x39e

    requires s0.stack[12] == 0x66

    requires s0.stack[13] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x39e;
      assert s1.Peek(12) == 0x66;
      assert s1.Peek(13) == 0x6b;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s7, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 66
    * Starting at 0x39e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x66

    requires s0.stack[10] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x66;
      assert s1.Peek(10) == 0x6b;
      var s2 := Swap2(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(10) == 0x66;
      assert s11.Peek(11) == 0x6b;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup10(s14);
      var s16 := Dup5(s15);
      var s17 := Gt(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x03b7);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s20, gas - 1)
      else
        ExecuteFromCFGNode_s34(s20, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 67
    * Starting at 0x3b4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x66

    requires s0.stack[11] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(11) == 0x66;
      assert s1.Peek(12) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 35
    * Segment Id for this node is: 68
    * Starting at 0x3b7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x66

    requires s0.stack[11] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x66;
      assert s1.Peek(11) == 0x6b;
      var s2 := Dup7(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s36(s6, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 69
    * Starting at 0x3bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x66

    requires s0.stack[11] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x66;
      assert s1.Peek(11) == 0x6b;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0488);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s7, gas - 1)
      else
        ExecuteFromCFGNode_s37(s7, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 70
    * Starting at 0x3c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x66

    requires s0.stack[11] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(11) == 0x66;
      assert s1.Peek(12) == 0x6b;
      var s2 := CallDataLoad(s1);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x03d4);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s8, gas - 1)
      else
        ExecuteFromCFGNode_s38(s8, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 71
    * Starting at 0x3d0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x66

    requires s0.stack[12] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(12) == 0x66;
      assert s1.Peek(13) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Dup2(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 39
    * Segment Id for this node is: 72
    * Starting at 0x3d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x66

    requires s0.stack[12] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x66;
      assert s1.Peek(12) == 0x6b;
      var s2 := Dup7(s1);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Dup3(s6);
      var s8 := Dup14(s7);
      var s9 := Sub(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(14) == 0x66;
      assert s11.Peek(15) == 0x6b;
      var s12 := Dup3(s11);
      var s13 := SGt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x03ec);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s16, gas - 1)
      else
        ExecuteFromCFGNode_s40(s16, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 73
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x66

    requires s0.stack[14] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(14) == 0x66;
      assert s1.Peek(15) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Dup2(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 41
    * Segment Id for this node is: 74
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x66

    requires s0.stack[14] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x66;
      assert s1.Peek(14) == 0x6b;
      var s2 := Push2(s1, 0x03f4);
      var s3 := Push2(s2, 0x02e8);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s4, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 51
    * Starting at 0x2e8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x3f4

    requires s0.stack[14] == 0x66

    requires s0.stack[15] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3f4;
      assert s1.Peek(14) == 0x66;
      assert s1.Peek(15) == 0x6b;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(4) == 0x3f4;
      assert s11.Peek(18) == 0x66;
      assert s11.Peek(19) == 0x6b;
      var s12 := Dup3(s11);
      var s13 := Lt(s12);
      var s14 := Or(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x030b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s17, gas - 1)
      else
        ExecuteFromCFGNode_s43(s17, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 52
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x3f4

    requires s0.stack[16] == 0x66

    requires s0.stack[17] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x030b);
      assert s1.Peek(0) == 0x30b;
      assert s1.Peek(3) == 0x3f4;
      assert s1.Peek(17) == 0x66;
      assert s1.Peek(18) == 0x6b;
      var s2 := Push2(s1, 0x02d4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s3, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 50
    * Starting at 0x2d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x30b

    requires s0.stack[3] == 0x3f4

    requires s0.stack[17] == 0x66

    requires s0.stack[18] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x30b;
      assert s1.Peek(3) == 0x3f4;
      assert s1.Peek(17) == 0x66;
      assert s1.Peek(18) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x30b;
      assert s11.Peek(5) == 0x3f4;
      assert s11.Peek(19) == 0x66;
      assert s11.Peek(20) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 45
    * Segment Id for this node is: 53
    * Starting at 0x30b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x3f4

    requires s0.stack[16] == 0x66

    requires s0.stack[17] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f4;
      assert s1.Peek(16) == 0x66;
      assert s1.Peek(17) == 0x6b;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s5, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 75
    * Starting at 0x3f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[14] == 0x66

    requires s0.stack[15] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x66;
      assert s1.Peek(15) == 0x6b;
      var s2 := Push2(s1, 0x03ff);
      var s3 := Dup12(s2);
      var s4 := Dup6(s3);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x0299);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s7, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 43
    * Starting at 0x299
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x3ff

    requires s0.stack[16] == 0x66

    requires s0.stack[17] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ff;
      assert s1.Peek(16) == 0x66;
      assert s1.Peek(17) == 0x6b;
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
      assert s11.Peek(4) == 0x3ff;
      assert s11.Peek(19) == 0x66;
      assert s11.Peek(20) == 0x6b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x02af);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s14, gas - 1)
      else
        ExecuteFromCFGNode_s48(s14, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 44
    * Starting at 0x2ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x3ff

    requires s0.stack[17] == 0x66

    requires s0.stack[18] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x3ff;
      assert s1.Peek(18) == 0x66;
      assert s1.Peek(19) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 49
    * Segment Id for this node is: 45
    * Starting at 0x2af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x3ff

    requires s0.stack[17] == 0x66

    requires s0.stack[18] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3ff;
      assert s1.Peek(17) == 0x66;
      assert s1.Peek(18) == 0x6b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s5, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 76
    * Starting at 0x3ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[15] == 0x66

    requires s0.stack[16] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(15) == 0x66;
      assert s1.Peek(16) == 0x6b;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Dup10(s7);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(16) == 0x66;
      assert s11.Peek(17) == 0x6b;
      var s12 := Push2(s11, 0x0412);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s13, gas - 1)
      else
        ExecuteFromCFGNode_s51(s13, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 77
    * Starting at 0x40e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[15] == 0x66

    requires s0.stack[16] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(16) == 0x66;
      assert s1.Peek(17) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Dup2(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 52
    * Segment Id for this node is: 78
    * Starting at 0x412
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 15
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x412 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[15] == 0x66

    requires s0.stack[16] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(15) == 0x66;
      assert s1.Peek(16) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap5(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Dup14(s7);
      var s9 := Push1(s8, 0x3f);
      var s10 := Dup6(s9);
      var s11 := Add(s10);
      assert s11.Peek(16) == 0x66;
      assert s11.Peek(17) == 0x6b;
      var s12 := SLt(s11);
      var s13 := Push2(s12, 0x0427);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s14, gas - 1)
      else
        ExecuteFromCFGNode_s53(s14, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 79
    * Starting at 0x423
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x423 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[14] == 0x66

    requires s0.stack[15] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(15) == 0x66;
      assert s1.Peek(16) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Dup2(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 54
    * Segment Id for this node is: 80
    * Starting at 0x427
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x427 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[14] == 0x66

    requires s0.stack[15] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x66;
      assert s1.Peek(15) == 0x6b;
      var s2 := Dup11(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Dup10(s5);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x043b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s11, gas - 1)
      else
        ExecuteFromCFGNode_s55(s11, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 81
    * Starting at 0x434
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[15] == 0x66

    requires s0.stack[16] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x043b);
      assert s1.Peek(0) == 0x43b;
      assert s1.Peek(16) == 0x66;
      assert s1.Peek(17) == 0x6b;
      var s2 := Push2(s1, 0x02d4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s3, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 50
    * Starting at 0x2d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x43b

    requires s0.stack[16] == 0x66

    requires s0.stack[17] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x43b;
      assert s1.Peek(16) == 0x66;
      assert s1.Peek(17) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x43b;
      assert s11.Peek(18) == 0x66;
      assert s11.Peek(19) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 57
    * Segment Id for this node is: 82
    * Starting at 0x43b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[15] == 0x66

    requires s0.stack[16] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(15) == 0x66;
      assert s1.Peek(16) == 0x6b;
      var s2 := Push2(s1, 0x044b);
      var s3 := Dup13(s2);
      var s4 := Dup5(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0311);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s11, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 54
    * Starting at 0x311
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x311 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x44b

    requires s0.stack[17] == 0x66

    requires s0.stack[18] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x44b;
      assert s1.Peek(17) == 0x66;
      assert s1.Peek(18) == 0x6b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x44b;
      assert s11.Peek(19) == 0x66;
      assert s11.Peek(20) == 0x6b;
      var s12 := Push8(s11, 0xffffffffffffffff);
      var s13 := Dup2(s12);
      var s14 := Gt(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Lt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x033a);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s21, gas - 1)
      else
        ExecuteFromCFGNode_s59(s21, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 55
    * Starting at 0x333
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x333 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x44b

    requires s0.stack[19] == 0x66

    requires s0.stack[20] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x033a);
      assert s1.Peek(0) == 0x33a;
      assert s1.Peek(4) == 0x44b;
      assert s1.Peek(20) == 0x66;
      assert s1.Peek(21) == 0x6b;
      var s2 := Push2(s1, 0x02d4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s3, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 50
    * Starting at 0x2d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x33a

    requires s0.stack[4] == 0x44b

    requires s0.stack[20] == 0x66

    requires s0.stack[21] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x33a;
      assert s1.Peek(4) == 0x44b;
      assert s1.Peek(20) == 0x66;
      assert s1.Peek(21) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x33a;
      assert s11.Peek(6) == 0x44b;
      assert s11.Peek(22) == 0x66;
      assert s11.Peek(23) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 61
    * Segment Id for this node is: 56
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x44b

    requires s0.stack[19] == 0x66

    requires s0.stack[20] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x44b;
      assert s1.Peek(19) == 0x66;
      assert s1.Peek(20) == 0x6b;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s7, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 83
    * Starting at 0x44b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 16
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[16] == 0x66

    requires s0.stack[17] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(16) == 0x66;
      assert s1.Peek(17) == 0x6b;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup15(s6);
      var s8 := Dup5(s7);
      var s9 := Dup3(s8);
      var s10 := Dup8(s9);
      var s11 := Add(s10);
      assert s11.Peek(18) == 0x66;
      assert s11.Peek(19) == 0x6b;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0461);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s16, gas - 1)
      else
        ExecuteFromCFGNode_s63(s16, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 84
    * Starting at 0x45d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[15] == 0x66

    requires s0.stack[16] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(16) == 0x66;
      assert s1.Peek(17) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Dup2(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 64
    * Segment Id for this node is: 85
    * Starting at 0x461
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x461 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[15] == 0x66

    requires s0.stack[16] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(15) == 0x66;
      assert s1.Peek(16) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Dup7(s3);
      var s5 := Add(s4);
      var s6 := Dup14(s5);
      var s7 := Dup6(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(16) == 0x66;
      assert s11.Peek(17) == 0x6b;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := Dup13(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Dup12(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(15) == 0x66;
      assert s21.Peek(16) == 0x6b;
      var s22 := Swap2(s21);
      var s23 := MStore(s22);
      var s24 := Dup5(s23);
      var s25 := MStore(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Swap2(s27);
      var s29 := Dup7(s28);
      var s30 := Add(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(10) == 0x66;
      assert s31.Peek(11) == 0x6b;
      var s32 := Swap1(s31);
      var s33 := Dup7(s32);
      var s34 := Add(s33);
      var s35 := Swap1(s34);
      var s36 := Push2(s35, 0x03bd);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s37, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 86
    * Starting at 0x488
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -10
    * Net Capacity Effect: +10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x488 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x66

    requires s0.stack[11] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x66;
      assert s1.Peek(11) == 0x6b;
      var s2 := Swap(s1, 10);
      var s3 := Swap(s2, 9);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x66;
      assert s11.Peek(3) == 0x6b;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s13, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 11
    * Starting at 0x66
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6b;
      var s2 := Push2(s1, 0x00ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s3, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 20
    * Starting at 0xed
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6b;
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Swap1(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x6b;
      var s12 := Dup2(s11);
      var s13 := Keccak256(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0xff);
      var s18 := And(s17);
      var s19 := IsZero(s18);
      var s20 := IsZero(s19);
      var s21 := Push1(s20, 0x01);
      assert s21.Peek(5) == 0x6b;
      var s22 := Eq(s21);
      var s23 := Push2(s22, 0x016c);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s24, gas - 1)
      else
        ExecuteFromCFGNode_s68(s24, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 21
    * Starting at 0x10c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x6b;
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
      assert s11.Peek(6) == 0x6b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x2c);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x55736572206973206e6f74207065726d697474656420746f2065786563757465);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x6b;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 12, 0x1020b3b3b932b3b0ba34b7b7);
      var s24 := Push1(s23, 0xa1);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x6b;
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

  /** Node 69
    * Segment Id for this node is: 22
    * Starting at 0x16c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6b;
      var s2 := Number(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Dup3(s4);
      var s6 := MLoad(s5);
      var s7 := Push8(s6, 0xffffffffffffffff);
      var s8 := Dup2(s7);
      var s9 := Gt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0189);
      assert s11.Peek(0) == 0x189;
      assert s11.Peek(6) == 0x6b;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s12, gas - 1)
      else
        ExecuteFromCFGNode_s70(s12, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 23
    * Starting at 0x182
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x182 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0189);
      assert s1.Peek(0) == 0x189;
      assert s1.Peek(5) == 0x6b;
      var s2 := Push2(s1, 0x02d4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s3, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 50
    * Starting at 0x2d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x189

    requires s0.stack[5] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x189;
      assert s1.Peek(5) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x189;
      assert s11.Peek(7) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 72
    * Segment Id for this node is: 24
    * Starting at 0x189
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x189 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Mul(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(7) == 0x6b;
      var s12 := Add(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x01bc);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s20, gas - 1)
      else
        ExecuteFromCFGNode_s73(s20, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 25
    * Starting at 0x1a3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0x6b;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s74(s3, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 26
    * Starting at 0x1a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x6b;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Swap1(s8);
      var s10 := Sub(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0x6b;
      var s12 := Dup2(s11);
      var s13 := Push2(s12, 0x01a7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s14, gas - 1)
      else
        ExecuteFromCFGNode_s75(s14, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 27
    * Starting at 0x1ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(6) == 0x6b;
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s76(s2, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 28
    * Starting at 0x1bc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x6b;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Push0(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s77(s5, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 29
    * Starting at 0x1c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b;
      var s2 := Dup4(s1);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0293);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s8, gas - 1)
      else
        ExecuteFromCFGNode_s78(s8, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 30
    * Starting at 0x1cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x6b;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Dup4(s3);
      var s5 := Dup2(s4);
      var s6 := MLoad(s5);
      var s7 := Dup2(s6);
      var s8 := Lt(s7);
      var s9 := Push2(s8, 0x01de);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s10, gas - 1)
      else
        ExecuteFromCFGNode_s79(s10, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 31
    * Starting at 0x1d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x01de);
      assert s1.Peek(0) == 0x1de;
      assert s1.Peek(9) == 0x6b;
      var s2 := Push2(s1, 0x0537);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s3, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 96
    * Starting at 0x537
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x1de

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1de;
      assert s1.Peek(9) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x1de;
      assert s11.Peek(11) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 81
    * Segment Id for this node is: 32
    * Starting at 0x1de
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x6b;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push0(s7);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(8) == 0x6b;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := And(s15);
      var s17 := Dup7(s16);
      var s18 := Dup5(s17);
      var s19 := Dup2(s18);
      var s20 := MLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(11) == 0x6b;
      var s22 := Lt(s21);
      var s23 := Push2(s22, 0x0204);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s24, gas - 1)
      else
        ExecuteFromCFGNode_s82(s24, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 33
    * Starting at 0x1fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0204);
      assert s1.Peek(0) == 0x204;
      assert s1.Peek(10) == 0x6b;
      var s2 := Push2(s1, 0x0537);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s3, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 96
    * Starting at 0x537
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x204

    requires s0.stack[10] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x204;
      assert s1.Peek(10) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x204;
      assert s11.Peek(12) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 84
    * Segment Id for this node is: 34
    * Starting at 0x204
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x204 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x6b;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(9) == 0x6b;
      var s12 := MLoad(s11);
      var s13 := Push2(s12, 0x021d);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x054b);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s17, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 97
    * Starting at 0x54b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x21d

    requires s0.stack[10] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x21d;
      assert s1.Peek(10) == 0x6b;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x055c);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0495);
      assert s11.Peek(0) == 0x495;
      assert s11.Peek(4) == 0x55c;
      assert s11.Peek(9) == 0x21d;
      assert s11.Peek(17) == 0x6b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s12, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 87
    * Starting at 0x495
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x495 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x55c

    requires s0.stack[8] == 0x21d

    requires s0.stack[16] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x55c;
      assert s1.Peek(8) == 0x21d;
      assert s1.Peek(16) == 0x6b;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s87(s2, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 88
    * Starting at 0x497
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x497 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x55c

    requires s0.stack[9] == 0x21d

    requires s0.stack[17] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x55c;
      assert s1.Peek(9) == 0x21d;
      assert s1.Peek(17) == 0x6b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04af);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s7, gas - 1)
      else
        ExecuteFromCFGNode_s88(s7, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 89
    * Starting at 0x4a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x55c

    requires s0.stack[9] == 0x21d

    requires s0.stack[17] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x55c;
      assert s1.Peek(10) == 0x21d;
      assert s1.Peek(18) == 0x6b;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0497);
      assert s11.Peek(0) == 0x497;
      assert s11.Peek(5) == 0x55c;
      assert s11.Peek(10) == 0x21d;
      assert s11.Peek(18) == 0x6b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s12, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 90
    * Starting at 0x4af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x55c

    requires s0.stack[9] == 0x21d

    requires s0.stack[17] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x55c;
      assert s1.Peek(9) == 0x21d;
      assert s1.Peek(17) == 0x6b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s8, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 98
    * Starting at 0x55c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x21d

    requires s0.stack[12] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x21d;
      assert s1.Peek(12) == 0x6b;
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
      ExecuteFromCFGNode_s91(s10, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 35
    * Starting at 0x21d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x6b;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push0(s8);
      var s10 := Dup7(s9);
      var s11 := Gas(s10);
      assert s11.Peek(15) == 0x6b;
      var s12 := Call(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := ReturnDataSize(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x0256);
      assert s21.Peek(0) == 0x256;
      assert s21.Peek(11) == 0x6b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s22, gas - 1)
      else
        ExecuteFromCFGNode_s92(s22, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 36
    * Starting at 0x236
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x236 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0x6b;
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
      assert s11.Peek(11) == 0x6b;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push0(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(13) == 0x6b;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x025b);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s25, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 38
    * Starting at 0x25b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x6b;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup1(s6);
      var s8 := Dup5(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := MLoad(s10);
      assert s11.Peek(10) == 0x6b;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x0273);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s15, gas - 1)
      else
        ExecuteFromCFGNode_s94(s15, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 39
    * Starting at 0x26c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0273);
      assert s1.Peek(0) == 0x273;
      assert s1.Peek(10) == 0x6b;
      var s2 := Push2(s1, 0x0537);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s3, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 96
    * Starting at 0x537
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x273

    requires s0.stack[10] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x273;
      assert s1.Peek(10) == 0x6b;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x273;
      assert s11.Peek(12) == 0x6b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 96
    * Segment Id for this node is: 40
    * Starting at 0x273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x6b;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0x6b;
      var s12 := Pop(s11);
      var s13 := Dup1(s12);
      var s14 := Dup1(s13);
      var s15 := Push2(s14, 0x028b);
      var s16 := Swap1(s15);
      var s17 := Push2(s16, 0x0566);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s18, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 99
    * Starting at 0x566
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x566 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x28b

    requires s0.stack[7] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x28b;
      assert s1.Peek(7) == 0x6b;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x0583);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s7, gas - 1)
      else
        ExecuteFromCFGNode_s98(s7, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 100
    * Starting at 0x570
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x570 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x28b

    requires s0.stack[8] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(3) == 0x28b;
      assert s1.Peek(9) == 0x6b;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 99
    * Segment Id for this node is: 101
    * Starting at 0x583
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x28b

    requires s0.stack[8] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x28b;
      assert s1.Peek(8) == 0x6b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s6, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 41
    * Starting at 0x28b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x6b;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x01c1);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s6, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 37
    * Starting at 0x256
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x6b;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s93(s4, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 42
    * Starting at 0x293
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x6b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s6, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 12
    * Starting at 0x6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0079);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x04b7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s9, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 91
    * Starting at 0x4b7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x79;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x79;
      var s12 := Dup6(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := Dup6(s15);
      var s17 := MLoad(s16);
      var s18 := Dup1(s17);
      var s19 := Dup5(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x60);
      assert s21.Peek(9) == 0x79;
      var s22 := Dup7(s21);
      var s23 := Add(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Push1(s25, 0x60);
      var s27 := Dup2(s26);
      var s28 := Push1(s27, 0x05);
      var s29 := Shl(s28);
      var s30 := Dup8(s29);
      var s31 := Add(s30);
      assert s31.Peek(10) == 0x79;
      var s32 := Add(s31);
      var s33 := Swap4(s32);
      var s34 := Pop(s33);
      var s35 := Dup3(s34);
      var s36 := Dup8(s35);
      var s37 := Add(s36);
      var s38 := Push0(s37);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s105(s38, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 92
    * Starting at 0x4e3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x79;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0529);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s7, gas - 1)
      else
        ExecuteFromCFGNode_s106(s7, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 93
    * Starting at 0x4ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup8(s0);
      assert s1.Peek(11) == 0x79;
      var s2 := Dup7(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x5f);
      var s5 := Not(s4);
      var s6 := Add(s5);
      var s7 := Dup5(s6);
      var s8 := MStore(s7);
      var s9 := Dup2(s8);
      var s10 := MLoad(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(12) == 0x79;
      var s12 := MLoad(s11);
      var s13 := Dup1(s12);
      var s14 := Dup9(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x050a);
      var s17 := Dup2(s16);
      var s18 := Dup9(s17);
      var s19 := Dup11(s18);
      var s20 := Add(s19);
      var s21 := Dup10(s20);
      assert s21.Peek(3) == 0x50a;
      assert s21.Peek(16) == 0x79;
      var s22 := Dup6(s21);
      var s23 := Add(s22);
      var s24 := Push2(s23, 0x0495);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s25, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 87
    * Starting at 0x495
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x495 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x50a

    requires s0.stack[16] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50a;
      assert s1.Peek(16) == 0x79;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s108(s2, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 88
    * Starting at 0x497
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x497 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x50a

    requires s0.stack[17] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(17) == 0x79;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04af);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s7, gas - 1)
      else
        ExecuteFromCFGNode_s109(s7, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 89
    * Starting at 0x4a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x50a

    requires s0.stack[17] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(18) == 0x79;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0497);
      assert s11.Peek(0) == 0x497;
      assert s11.Peek(5) == 0x50a;
      assert s11.Peek(18) == 0x79;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s12, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 90
    * Starting at 0x4af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x50a

    requires s0.stack[17] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(17) == 0x79;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s8, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 94
    * Starting at 0x50a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x79;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Swap7(s6);
      var s8 := Swap1(s7);
      var s9 := Swap7(s8);
      var s10 := Add(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(12) == 0x79;
      var s12 := Add(s11);
      var s13 := Swap6(s12);
      var s14 := Pop(s13);
      var s15 := Swap3(s14);
      var s16 := Dup5(s15);
      var s17 := Add(s16);
      var s18 := Swap3(s17);
      var s19 := Swap1(s18);
      var s20 := Dup5(s19);
      var s21 := Add(s20);
      assert s21.Peek(10) == 0x79;
      var s22 := Swap1(s21);
      var s23 := Push1(s22, 0x01);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x04e3);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s26, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 95
    * Starting at 0x529
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -10
    * Net Capacity Effect: +10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x529 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x79

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x79;
      var s2 := Pop(s1);
      var s3 := Swap4(s2);
      var s4 := Swap(s3, 9);
      var s5 := Swap(s4, 8);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x79;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s14, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 13
    * Starting at 0x79
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
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

  /** Node 114
    * Segment Id for this node is: 7
    * Starting at 0x43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0056);
      var s3 := Push2(s2, 0x0051);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x02b4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s7, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 46
    * Starting at 0x2b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x51

    requires s0.stack[3] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x51;
      assert s1.Peek(3) == 0x56;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02c4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s10, gas - 1)
      else
        ExecuteFromCFGNode_s116(s10, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 47
    * Starting at 0x2c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x51

    requires s0.stack[4] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x51;
      assert s1.Peek(5) == 0x56;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 117
    * Segment Id for this node is: 48
    * Starting at 0x2c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x51

    requires s0.stack[4] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x51;
      assert s1.Peek(4) == 0x56;
      var s2 := Push2(s1, 0x02cd);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0299);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s5, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 43
    * Starting at 0x299
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x2cd

    requires s0.stack[5] == 0x51

    requires s0.stack[6] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2cd;
      assert s1.Peek(5) == 0x51;
      assert s1.Peek(6) == 0x56;
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
      assert s11.Peek(4) == 0x2cd;
      assert s11.Peek(8) == 0x51;
      assert s11.Peek(9) == 0x56;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x02af);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s120(s14, gas - 1)
      else
        ExecuteFromCFGNode_s119(s14, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 44
    * Starting at 0x2ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x2cd

    requires s0.stack[6] == 0x51

    requires s0.stack[7] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x2cd;
      assert s1.Peek(7) == 0x51;
      assert s1.Peek(8) == 0x56;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 120
    * Segment Id for this node is: 45
    * Starting at 0x2af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x2cd

    requires s0.stack[6] == 0x51

    requires s0.stack[7] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2cd;
      assert s1.Peek(6) == 0x51;
      assert s1.Peek(7) == 0x56;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s5, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 49
    * Starting at 0x2cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x51

    requires s0.stack[5] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x51;
      assert s1.Peek(5) == 0x56;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s7, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 8
    * Starting at 0x51
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x56;
      var s2 := Push2(s1, 0x00b4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s3, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 17
    * Starting at 0xb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x56;
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(2) == 0x56;
      var s12 := Push2(s11, 0x00ca);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s13, gas - 1)
      else
        ExecuteFromCFGNode_s124(s13, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 18
    * Starting at 0xc7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x56;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 125
    * Segment Id for this node is: 19
    * Starting at 0xca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x56;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push0(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x56;
      var s12 := Push1(s11, 0x20);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := Dup1(s18);
      var s20 := SLoad(s19);
      var s21 := Push1(s20, 0xff);
      assert s21.Peek(3) == 0x56;
      var s22 := Not(s21);
      var s23 := And(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Or(s24);
      var s26 := Swap1(s25);
      var s27 := SStore(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s28, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 9
    * Starting at 0x56
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56 as nat
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

  /** Node 127
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
