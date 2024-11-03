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
      var s4 := Push2(s3, 0x000c);
      var s5 := Push2(s4, 0x000e);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s1(s6, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 2
    * Starting at 0xe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc;
      var s2 := Push32(s1, 0x000000000000000000000000c6b60cbcec7d9f98fdcdef6b9a611a955d7fefd4);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Caller(s8);
      var s10 := Sub(s9);
      var s11 := Push2(s10, 0x007a);
      assert s11.Peek(0) == 0x7a;
      assert s11.Peek(2) == 0xc;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s12, gas - 1)
      else
        ExecuteFromCFGNode_s2(s12, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 3
    * Starting at 0x3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(1) == 0xc;
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Push4(s9, 0x278f7943);
      var s11 := Push1(s10, 0xe1);
      assert s11.Peek(3) == 0xc;
      var s12 := Shl(s11);
      var s13 := Eq(s12);
      var s14 := Push2(s13, 0x0070);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s4(s15, gas - 1)
      else
        ExecuteFromCFGNode_s3(s15, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 4
    * Starting at 0x58
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0xc;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x34ad5dbb);
      var s4 := Push1(s3, 0xe2);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(2) == 0xc;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 4
    * Segment Id for this node is: 5
    * Starting at 0x70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc;
      var s2 := Push2(s1, 0x0078);
      var s3 := Push2(s2, 0x0082);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s5(s4, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 8
    * Starting at 0x82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x78

    requires s0.stack[1] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x78;
      assert s1.Peek(1) == 0xc;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0091);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Dup2(s6);
      var s8 := Dup5(s7);
      var s9 := Push2(s8, 0x0303);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s6(s10, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 48
    * Starting at 0x303
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x303 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x91

    requires s0.stack[7] == 0x78

    requires s0.stack[8] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x91;
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0xc;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0311);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s9, gas - 1)
      else
        ExecuteFromCFGNode_s7(s9, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 49
    * Starting at 0x30e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0xc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 8
    * Segment Id for this node is: 50
    * Starting at 0x311
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x311 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0xc;
      var s2 := Dup4(s1);
      var s3 := Dup7(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x031d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s7, gas - 1)
      else
        ExecuteFromCFGNode_s9(s7, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 51
    * Starting at 0x31a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0xc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 10
    * Segment Id for this node is: 52
    * Starting at 0x31d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0xc;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap4(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := Sub(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(1) == 0x91;
      assert s11.Peek(6) == 0x78;
      assert s11.Peek(7) == 0xc;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s13, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 9
    * Starting at 0x91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x78

    requires s0.stack[5] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78;
      assert s1.Peek(5) == 0xc;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x009e);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x033e);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s9, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 54
    * Starting at 0x33e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x9e

    requires s0.stack[5] == 0x78

    requires s0.stack[6] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9e;
      assert s1.Peek(5) == 0x78;
      assert s1.Peek(6) == 0xc;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x034f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s11, gas - 1)
      else
        ExecuteFromCFGNode_s13(s11, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 55
    * Starting at 0x34c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x9e

    requires s0.stack[7] == 0x78

    requires s0.stack[8] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x9e;
      assert s1.Peek(8) == 0x78;
      assert s1.Peek(9) == 0xc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 14
    * Segment Id for this node is: 56
    * Starting at 0x34f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x9e

    requires s0.stack[7] == 0x78

    requires s0.stack[8] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9e;
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0xc;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x9e;
      assert s11.Peek(10) == 0x78;
      assert s11.Peek(11) == 0xc;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0365);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s14, gas - 1)
      else
        ExecuteFromCFGNode_s15(s14, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 57
    * Starting at 0x362
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x362 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x9e

    requires s0.stack[8] == 0x78

    requires s0.stack[9] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x9e;
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0xc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 16
    * Segment Id for this node is: 58
    * Starting at 0x365
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x9e

    requires s0.stack[8] == 0x78

    requires s0.stack[9] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9e;
      assert s1.Peek(8) == 0x78;
      assert s1.Peek(9) == 0xc;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(7) == 0x9e;
      assert s11.Peek(10) == 0x78;
      assert s11.Peek(11) == 0xc;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0381);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s14, gas - 1)
      else
        ExecuteFromCFGNode_s17(s14, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 59
    * Starting at 0x37e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x9e

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x9e;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0xc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 18
    * Segment Id for this node is: 60
    * Starting at 0x381
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x381 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x9e

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x9e;
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0xc;
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
      assert s11.Peek(7) == 0x9e;
      assert s11.Peek(10) == 0x78;
      assert s11.Peek(11) == 0xc;
      var s12 := Push2(s11, 0x0394);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s13, gas - 1)
      else
        ExecuteFromCFGNode_s19(s13, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 61
    * Starting at 0x391
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x391 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x9e

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x9e;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0xc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 20
    * Segment Id for this node is: 62
    * Starting at 0x394
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x394 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x9e

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x9e;
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0xc;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x03a6);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s9, gas - 1)
      else
        ExecuteFromCFGNode_s21(s9, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 63
    * Starting at 0x39f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x9e

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03a6);
      assert s1.Peek(0) == 0x3a6;
      assert s1.Peek(8) == 0x9e;
      assert s1.Peek(11) == 0x78;
      assert s1.Peek(12) == 0xc;
      var s2 := Push2(s1, 0x032a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 53
    * Starting at 0x32a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x3a6

    requires s0.stack[8] == 0x9e

    requires s0.stack[11] == 0x78

    requires s0.stack[12] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3a6;
      assert s1.Peek(8) == 0x9e;
      assert s1.Peek(11) == 0x78;
      assert s1.Peek(12) == 0xc;
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
      assert s11.Peek(2) == 0x3a6;
      assert s11.Peek(10) == 0x9e;
      assert s11.Peek(13) == 0x78;
      assert s11.Peek(14) == 0xc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 23
    * Segment Id for this node is: 64
    * Starting at 0x3a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x9e

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x9e;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0xc;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(10) == 0x9e;
      assert s11.Peek(13) == 0x78;
      assert s11.Peek(14) == 0xc;
      var s12 := Push1(s11, 0x3f);
      var s13 := Add(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Dup4(s17);
      var s19 := Dup3(s18);
      var s20 := Gt(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(11) == 0x9e;
      assert s21.Peek(14) == 0x78;
      assert s21.Peek(15) == 0xc;
      var s22 := Dup4(s21);
      var s23 := Lt(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := Push2(s25, 0x03ce);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s27, gas - 1)
      else
        ExecuteFromCFGNode_s24(s27, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 65
    * Starting at 0x3c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x9e

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03ce);
      assert s1.Peek(0) == 0x3ce;
      assert s1.Peek(10) == 0x9e;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0xc;
      var s2 := Push2(s1, 0x032a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s3, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 53
    * Starting at 0x32a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x3ce

    requires s0.stack[10] == 0x9e

    requires s0.stack[13] == 0x78

    requires s0.stack[14] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3ce;
      assert s1.Peek(10) == 0x9e;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0xc;
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
      assert s11.Peek(2) == 0x3ce;
      assert s11.Peek(12) == 0x9e;
      assert s11.Peek(15) == 0x78;
      assert s11.Peek(16) == 0xc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 26
    * Segment Id for this node is: 66
    * Starting at 0x3ce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x9e

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x9e;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0xc;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup3(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup9(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup5(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(13) == 0x9e;
      assert s11.Peek(16) == 0x78;
      assert s11.Peek(17) == 0xc;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x03e6);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s17, gas - 1)
      else
        ExecuteFromCFGNode_s27(s17, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 67
    * Starting at 0x3e3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x9e

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(10) == 0x9e;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0xc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 28
    * Segment Id for this node is: 68
    * Starting at 0x3e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x9e

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x9e;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0xc;
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup7(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push0(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x9e;
      assert s11.Peek(14) == 0x78;
      assert s11.Peek(15) == 0xc;
      var s12 := Dup5(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap6(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(7) == 0x9e;
      assert s21.Peek(10) == 0x78;
      assert s21.Peek(11) == 0xc;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Swap3(s24);
      var s26 := Pop(s25);
      var s27 := Swap3(s26);
      var s28 := Swap1(s27);
      var s29 := Pop(s28);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s30, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 10
    * Starting at 0x9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x78

    requires s0.stack[5] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78;
      assert s1.Peek(5) == 0xc;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x00ac);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Push2(s8, 0x00c0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s10, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 14
    * Starting at 0xc0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xac

    requires s0.stack[5] == 0x78

    requires s0.stack[6] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac;
      assert s1.Peek(5) == 0x78;
      assert s1.Peek(6) == 0xc;
      var s2 := Push2(s1, 0x00c9);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x016f);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s5, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 24
    * Starting at 0x16f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xc9

    requires s0.stack[4] == 0xac

    requires s0.stack[7] == 0x78

    requires s0.stack[8] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      assert s1.Peek(4) == 0xac;
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0xc;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := ExtCodeSize(s8);
      var s10 := Push0(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0xc9;
      assert s11.Peek(5) == 0xac;
      assert s11.Peek(8) == 0x78;
      assert s11.Peek(9) == 0xc;
      var s12 := Push2(s11, 0x01a9);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s13, gas - 1)
      else
        ExecuteFromCFGNode_s32(s13, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 25
    * Starting at 0x181
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x181 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xc9

    requires s0.stack[4] == 0xac

    requires s0.stack[7] == 0x78

    requires s0.stack[8] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xc9;
      assert s1.Peek(5) == 0xac;
      assert s1.Peek(8) == 0x78;
      assert s1.Peek(9) == 0xc;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x4c9c8ce3);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(4) == 0xc9;
      assert s11.Peek(7) == 0xac;
      assert s11.Peek(10) == 0x78;
      assert s11.Peek(11) == 0xc;
      var s12 := Sub(s11);
      var s13 := Dup3(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x04);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x24);
      var s20 := Add(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s33(s20, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 26
    * Starting at 0x1a0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xc9

    requires s0.stack[5] == 0xac

    requires s0.stack[8] == 0x78

    requires s0.stack[9] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc9;
      assert s1.Peek(5) == 0xac;
      assert s1.Peek(8) == 0x78;
      assert s1.Peek(9) == 0xc;
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

  /** Node 34
    * Segment Id for this node is: 27
    * Starting at 0x1a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xc9

    requires s0.stack[4] == 0xac

    requires s0.stack[7] == 0x78

    requires s0.stack[8] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      assert s1.Peek(4) == 0xac;
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0xc;
      var s2 := Push32(s1, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Not(s9);
      var s11 := And(s10);
      assert s11.Peek(3) == 0xc9;
      assert s11.Peek(6) == 0xac;
      assert s11.Peek(9) == 0x78;
      assert s11.Peek(10) == 0xc;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Swap3(s16);
      var s18 := Swap1(s17);
      var s19 := Swap3(s18);
      var s20 := And(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(3) == 0xc9;
      assert s21.Peek(6) == 0xac;
      assert s21.Peek(9) == 0x78;
      assert s21.Peek(10) == 0xc;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := Or(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s27, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 15
    * Starting at 0xc9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xac

    requires s0.stack[5] == 0x78

    requires s0.stack[6] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac;
      assert s1.Peek(5) == 0x78;
      assert s1.Peek(6) == 0xc;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := And(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0xac;
      assert s11.Peek(7) == 0x78;
      assert s11.Peek(8) == 0xc;
      var s12 := Push32(s11, 0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b);
      var s13 := Swap1(s12);
      var s14 := Push0(s13);
      var s15 := Swap1(s14);
      var s16 := Log2(s15);
      var s17 := Dup1(s16);
      var s18 := MLoad(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0112);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s21, gas - 1)
      else
        ExecuteFromCFGNode_s36(s21, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 16
    * Starting at 0x104
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xac

    requires s0.stack[5] == 0x78

    requires s0.stack[6] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x010d);
      assert s1.Peek(0) == 0x10d;
      assert s1.Peek(3) == 0xac;
      assert s1.Peek(6) == 0x78;
      assert s1.Peek(7) == 0xc;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x01ea);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s5, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 28
    * Starting at 0x1ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x10d

    requires s0.stack[5] == 0xac

    requires s0.stack[8] == 0x78

    requires s0.stack[9] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10d;
      assert s1.Peek(5) == 0xac;
      assert s1.Peek(8) == 0x78;
      assert s1.Peek(9) == 0xc;
      var s2 := Push1(s1, 0x60);
      var s3 := Push0(s2);
      var s4 := Dup1(s3);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x10d;
      assert s11.Peek(9) == 0xac;
      assert s11.Peek(12) == 0x78;
      assert s11.Peek(13) == 0xc;
      var s12 := Dup5(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0206);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0407);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s19, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 69
    * Starting at 0x407
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x407 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x206

    requires s0.stack[9] == 0x10d

    requires s0.stack[12] == 0xac

    requires s0.stack[15] == 0x78

    requires s0.stack[16] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x206;
      assert s1.Peek(9) == 0x10d;
      assert s1.Peek(12) == 0xac;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0xc;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push0(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s39(s5, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 70
    * Starting at 0x40c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x206

    requires s0.stack[12] == 0x10d

    requires s0.stack[15] == 0xac

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x206;
      assert s1.Peek(12) == 0x10d;
      assert s1.Peek(15) == 0xac;
      assert s1.Peek(18) == 0x78;
      assert s1.Peek(19) == 0xc;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0426);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s7, gas - 1)
      else
        ExecuteFromCFGNode_s40(s7, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 71
    * Starting at 0x415
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x415 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x206

    requires s0.stack[12] == 0x10d

    requires s0.stack[15] == 0xac

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x206;
      assert s1.Peek(13) == 0x10d;
      assert s1.Peek(16) == 0xac;
      assert s1.Peek(19) == 0x78;
      assert s1.Peek(20) == 0xc;
      var s2 := Dup2(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup6(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x206;
      assert s11.Peek(13) == 0x10d;
      assert s11.Peek(16) == 0xac;
      assert s11.Peek(19) == 0x78;
      assert s11.Peek(20) == 0xc;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x040c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s14, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 72
    * Starting at 0x426
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x426 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x206

    requires s0.stack[12] == 0x10d

    requires s0.stack[15] == 0xac

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x206;
      assert s1.Peek(12) == 0x10d;
      assert s1.Peek(15) == 0xac;
      assert s1.Peek(18) == 0x78;
      assert s1.Peek(19) == 0xc;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap2(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x206;
      assert s11.Peek(9) == 0x10d;
      assert s11.Peek(12) == 0xac;
      assert s11.Peek(15) == 0x78;
      assert s11.Peek(16) == 0xc;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s13, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 29
    * Starting at 0x206
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x206 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x10d

    requires s0.stack[10] == 0xac

    requires s0.stack[13] == 0x78

    requires s0.stack[14] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x10d;
      assert s1.Peek(10) == 0xac;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0xc;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup6(s8);
      var s10 := Gas(s9);
      var s11 := DelegateCall(s10);
      assert s11.Peek(8) == 0x10d;
      assert s11.Peek(11) == 0xac;
      assert s11.Peek(14) == 0x78;
      assert s11.Peek(15) == 0xc;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup1(s15);
      var s17 := Push0(s16);
      var s18 := Dup2(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x023e);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s62(s21, gas - 1)
      else
        ExecuteFromCFGNode_s43(s21, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 30
    * Starting at 0x21e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x10d

    requires s0.stack[11] == 0xac

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x10d;
      assert s1.Peek(12) == 0xac;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0xc;
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
      assert s11.Peek(10) == 0x10d;
      assert s11.Peek(13) == 0xac;
      assert s11.Peek(16) == 0x78;
      assert s11.Peek(17) == 0xc;
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
      assert s21.Peek(12) == 0x10d;
      assert s21.Peek(15) == 0xac;
      assert s21.Peek(18) == 0x78;
      assert s21.Peek(19) == 0xc;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0243);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s25, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 32
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x10d

    requires s0.stack[11] == 0xac

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x10d;
      assert s1.Peek(11) == 0xac;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0xc;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0253);
      var s8 := Dup6(s7);
      var s9 := Dup4(s8);
      var s10 := Dup4(s9);
      var s11 := Push2(s10, 0x027b);
      assert s11.Peek(0) == 0x27b;
      assert s11.Peek(4) == 0x253;
      assert s11.Peek(10) == 0x10d;
      assert s11.Peek(13) == 0xac;
      assert s11.Peek(16) == 0x78;
      assert s11.Peek(17) == 0xc;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s12, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 36
    * Starting at 0x27b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x253

    requires s0.stack[9] == 0x10d

    requires s0.stack[12] == 0xac

    requires s0.stack[15] == 0x78

    requires s0.stack[16] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x253;
      assert s1.Peek(9) == 0x10d;
      assert s1.Peek(12) == 0xac;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0xc;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0290);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s5, gas - 1)
      else
        ExecuteFromCFGNode_s46(s5, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 37
    * Starting at 0x283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x253

    requires s0.stack[10] == 0x10d

    requires s0.stack[13] == 0xac

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x028b);
      assert s1.Peek(0) == 0x28b;
      assert s1.Peek(5) == 0x253;
      assert s1.Peek(11) == 0x10d;
      assert s1.Peek(14) == 0xac;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0xc;
      var s2 := Dup3(s1);
      var s3 := Push2(s2, 0x02da);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s4, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 45
    * Starting at 0x2da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x28b

    requires s0.stack[6] == 0x253

    requires s0.stack[12] == 0x10d

    requires s0.stack[15] == 0xac

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x28b;
      assert s1.Peek(6) == 0x253;
      assert s1.Peek(12) == 0x10d;
      assert s1.Peek(15) == 0xac;
      assert s1.Peek(18) == 0x78;
      assert s1.Peek(19) == 0xc;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x02ea);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s6, gas - 1)
      else
        ExecuteFromCFGNode_s48(s6, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 46
    * Starting at 0x2e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x28b

    requires s0.stack[6] == 0x253

    requires s0.stack[12] == 0x10d

    requires s0.stack[15] == 0xac

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(2) == 0x28b;
      assert s1.Peek(7) == 0x253;
      assert s1.Peek(13) == 0x10d;
      assert s1.Peek(16) == 0xac;
      assert s1.Peek(19) == 0x78;
      assert s1.Peek(20) == 0xc;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 49
    * Segment Id for this node is: 47
    * Starting at 0x2ea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x28b

    requires s0.stack[6] == 0x253

    requires s0.stack[12] == 0x10d

    requires s0.stack[15] == 0xac

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x28b;
      assert s1.Peek(6) == 0x253;
      assert s1.Peek(12) == 0x10d;
      assert s1.Peek(15) == 0xac;
      assert s1.Peek(18) == 0x78;
      assert s1.Peek(19) == 0xc;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x0a12f521);
      var s5 := Push1(s4, 0xe1);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x28b;
      assert s11.Peek(8) == 0x253;
      assert s11.Peek(14) == 0x10d;
      assert s11.Peek(17) == 0xac;
      assert s11.Peek(20) == 0x78;
      assert s11.Peek(21) == 0xc;
      var s12 := MLoad(s11);
      var s13 := Dup1(s12);
      var s14 := Swap2(s13);
      var s15 := Sub(s14);
      var s16 := Swap1(s15);
      var s17 := Revert(s16);
      // Segment is terminal (Revert, Stop or Return)
      s17
  }

  /** Node 50
    * Segment Id for this node is: 39
    * Starting at 0x290
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x290 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x253

    requires s0.stack[10] == 0x10d

    requires s0.stack[13] == 0xac

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x253;
      assert s1.Peek(10) == 0x10d;
      assert s1.Peek(13) == 0xac;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0xc;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x02a7);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s8, gas - 1)
      else
        ExecuteFromCFGNode_s51(s8, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 40
    * Starting at 0x29a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x253

    requires s0.stack[11] == 0x10d

    requires s0.stack[14] == 0xac

    requires s0.stack[17] == 0x78

    requires s0.stack[18] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x253;
      assert s1.Peek(10) == 0x10d;
      assert s1.Peek(13) == 0xac;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0xc;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup5(s6);
      var s8 := And(s7);
      var s9 := ExtCodeSize(s8);
      var s10 := IsZero(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s52(s10, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 41
    * Starting at 0x2a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x253

    requires s0.stack[11] == 0x10d

    requires s0.stack[14] == 0xac

    requires s0.stack[17] == 0x78

    requires s0.stack[18] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x253;
      assert s1.Peek(11) == 0x10d;
      assert s1.Peek(14) == 0xac;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0xc;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x02d0);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s4, gas - 1)
      else
        ExecuteFromCFGNode_s53(s4, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 42
    * Starting at 0x2ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x253

    requires s0.stack[10] == 0x10d

    requires s0.stack[13] == 0xac

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x253;
      assert s1.Peek(11) == 0x10d;
      assert s1.Peek(14) == 0xac;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0xc;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x9996b315);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(7) == 0x253;
      assert s11.Peek(13) == 0x10d;
      assert s11.Peek(16) == 0xac;
      assert s11.Peek(19) == 0x78;
      assert s11.Peek(20) == 0xc;
      var s12 := Sub(s11);
      var s13 := Dup6(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x04);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x24);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x01a0);
      assert s21.Peek(0) == 0x1a0;
      assert s21.Peek(6) == 0x253;
      assert s21.Peek(12) == 0x10d;
      assert s21.Peek(15) == 0xac;
      assert s21.Peek(18) == 0x78;
      assert s21.Peek(19) == 0xc;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s22, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 26
    * Starting at 0x1a0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x253

    requires s0.stack[11] == 0x10d

    requires s0.stack[14] == 0xac

    requires s0.stack[17] == 0x78

    requires s0.stack[18] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x253;
      assert s1.Peek(11) == 0x10d;
      assert s1.Peek(14) == 0xac;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0xc;
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

  /** Node 55
    * Segment Id for this node is: 43
    * Starting at 0x2d0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x253

    requires s0.stack[10] == 0x10d

    requires s0.stack[13] == 0xac

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x253;
      assert s1.Peek(10) == 0x10d;
      assert s1.Peek(13) == 0xac;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0xc;
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s56(s3, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 44
    * Starting at 0x2d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x253

    requires s0.stack[10] == 0x10d

    requires s0.stack[13] == 0xac

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x253;
      assert s1.Peek(10) == 0x10d;
      assert s1.Peek(13) == 0xac;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0xc;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s7, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 33
    * Starting at 0x253
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x253 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x10d

    requires s0.stack[9] == 0xac

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x10d;
      assert s1.Peek(9) == 0xac;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0xc;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s9, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 17
    * Starting at 0x10d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xac

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xac;
      assert s1.Peek(6) == 0x78;
      assert s1.Peek(7) == 0xc;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s5, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 11
    * Starting at 0xac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x78

    requires s0.stack[3] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x78;
      assert s1.Peek(3) == 0xc;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s4, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 6
    * Starting at 0x78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s2, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 1
    * Starting at 0xc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Stop(s1);
      // Segment is terminal (Revert, Stop or Return)
      s2
  }

  /** Node 62
    * Segment Id for this node is: 31
    * Starting at 0x23e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x10d

    requires s0.stack[11] == 0xac

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x10d;
      assert s1.Peek(11) == 0xac;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0xc;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s44(s4, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 18
    * Starting at 0x112
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xac

    requires s0.stack[5] == 0x78

    requires s0.stack[6] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac;
      assert s1.Peek(5) == 0x78;
      assert s1.Peek(6) == 0xc;
      var s2 := Push2(s1, 0x00ac);
      var s3 := Push2(s2, 0x025c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s4, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 34
    * Starting at 0x25c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xac

    requires s0.stack[3] == 0xac

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xac;
      assert s1.Peek(3) == 0xac;
      assert s1.Peek(6) == 0x78;
      assert s1.Peek(7) == 0xc;
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0078);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s5, gas - 1)
      else
        ExecuteFromCFGNode_s65(s5, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 35
    * Starting at 0x263
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x263 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xac

    requires s0.stack[3] == 0xac

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0xac;
      assert s1.Peek(4) == 0xac;
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0xc;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0xb398979f);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(2) == 0xac;
      assert s11.Peek(5) == 0xac;
      assert s11.Peek(8) == 0x78;
      assert s11.Peek(9) == 0xc;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 66
    * Segment Id for this node is: 6
    * Starting at 0x78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xac

    requires s0.stack[3] == 0xac

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xac;
      assert s1.Peek(3) == 0xac;
      assert s1.Peek(6) == 0x78;
      assert s1.Peek(7) == 0xc;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s2, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 11
    * Starting at 0xac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xac

    requires s0.stack[5] == 0x78

    requires s0.stack[6] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac;
      assert s1.Peek(5) == 0x78;
      assert s1.Peek(6) == 0xc;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s4, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 7
    * Starting at 0x7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc;
      var s2 := Push2(s1, 0x0078);
      var s3 := Push2(s2, 0x00b0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s4, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 12
    * Starting at 0xb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x78

    requires s0.stack[1] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x78;
      assert s1.Peek(1) == 0xc;
      var s2 := Push2(s1, 0x0078);
      var s3 := Push2(s2, 0x00bb);
      var s4 := Push2(s3, 0x011a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s5, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 19
    * Starting at 0x11a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0xbb

    requires s0.stack[1] == 0x78

    requires s0.stack[2] == 0x78

    requires s0.stack[3] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbb;
      assert s1.Peek(1) == 0x78;
      assert s1.Peek(2) == 0x78;
      assert s1.Peek(3) == 0xc;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x014c);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(1) == 0x14c;
      assert s11.Peek(3) == 0xbb;
      assert s11.Peek(4) == 0x78;
      assert s11.Peek(5) == 0x78;
      assert s11.Peek(6) == 0xc;
      var s12 := Swap1(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s13, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 20
    * Starting at 0x14c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0xbb

    requires s0.stack[3] == 0x78

    requires s0.stack[4] == 0x78

    requires s0.stack[5] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbb;
      assert s1.Peek(3) == 0x78;
      assert s1.Peek(4) == 0x78;
      assert s1.Peek(5) == 0xc;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s5, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 13
    * Starting at 0xbb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x78

    requires s0.stack[2] == 0x78

    requires s0.stack[3] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x78;
      assert s1.Peek(2) == 0x78;
      assert s1.Peek(3) == 0xc;
      var s2 := Push2(s1, 0x0151);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 21
    * Starting at 0x151
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x78

    requires s0.stack[2] == 0x78

    requires s0.stack[3] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x78;
      assert s1.Peek(2) == 0x78;
      assert s1.Peek(3) == 0xc;
      var s2 := CallDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Dup1(s3);
      var s5 := CallDataCopy(s4);
      var s6 := Push0(s5);
      var s7 := Dup1(s6);
      var s8 := CallDataSize(s7);
      var s9 := Push0(s8);
      var s10 := Dup5(s9);
      var s11 := Gas(s10);
      assert s11.Peek(7) == 0x78;
      assert s11.Peek(8) == 0x78;
      assert s11.Peek(9) == 0xc;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x016b);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s21, gas - 1)
      else
        ExecuteFromCFGNode_s74(s21, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 22
    * Starting at 0x168
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x168 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x78

    requires s0.stack[4] == 0x78

    requires s0.stack[5] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x78;
      assert s1.Peek(5) == 0x78;
      assert s1.Peek(6) == 0xc;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 75
    * Segment Id for this node is: 23
    * Starting at 0x16b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x78

    requires s0.stack[4] == 0x78

    requires s0.stack[5] == 0xc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x78;
      assert s1.Peek(4) == 0x78;
      assert s1.Peek(5) == 0xc;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
