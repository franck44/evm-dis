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
      var s7 := Push2(s6, 0x00c2);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s8, gas - 1)
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
      var s6 := Push4(s5, 0x831e80f2);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x007f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s9, gas - 1)
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
      var s2 := Push4(s1, 0xd784d426);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0059);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd784d426);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0241);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd9eb5947);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0261);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0277);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x4a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf46901ed);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0297);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x55
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55 as nat
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

  /** Node 8
    * Segment Id for this node is: 62
    * Starting at 0x297
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x297 as nat
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
      var s5 := Push2(s4, 0x02a3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 63
    * Starting at 0x29f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
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

  /** Node 10
    * Segment Id for this node is: 64
    * Starting at 0x2a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0163);
      var s4 := Push2(s3, 0x02b2);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0ae1);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s8, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 158
    * Starting at 0xae1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2b2

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2b2;
      assert s1.Peek(3) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0af3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s10, gas - 1)
      else
        ExecuteFromCFGNode_s12(s10, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 159
    * Starting at 0xaef
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x2b2

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2b2;
      assert s1.Peek(5) == 0x163;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 13
    * Segment Id for this node is: 160
    * Starting at 0xaf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x2b2

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2b2;
      assert s1.Peek(4) == 0x163;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2b2;
      assert s11.Peek(7) == 0x163;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b0a);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s14, gas - 1)
      else
        ExecuteFromCFGNode_s14(s14, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 161
    * Starting at 0xb06
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2b2

    requires s0.stack[5] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x2b2;
      assert s1.Peek(6) == 0x163;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 15
    * Segment Id for this node is: 162
    * Starting at 0xb0a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2b2

    requires s0.stack[5] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2b2;
      assert s1.Peek(5) == 0x163;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s7, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 65
    * Starting at 0x2b2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x05bd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s3, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 102
    * Starting at 0x5bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x05c5);
      var s3 := Push2(s2, 0x062e);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s4, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 108
    * Starting at 0x62e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x5c5

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5c5;
      assert s1.Peek(2) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x5c5;
      assert s11.Peek(3) == 0x163;
      var s12 := Push2(s11, 0x031e);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s13, gas - 1)
      else
        ExecuteFromCFGNode_s19(s13, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 109
    * Starting at 0x641
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x641 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x5c5

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x5c5;
      assert s1.Peek(3) == 0x163;
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
      assert s11.Peek(3) == 0x5c5;
      assert s11.Peek(5) == 0x163;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x5c5;
      assert s21.Peek(6) == 0x163;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x02fe);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s27, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5c5

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5c5;
      assert s1.Peek(3) == 0x163;
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

  /** Node 21
    * Segment Id for this node is: 73
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x5c5

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5c5;
      assert s1.Peek(2) == 0x163;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s2, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 103
    * Starting at 0x5c5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := IsZero(s8);
      var s10 := Dup1(s9);
      var s11 := Push2(s10, 0x05e3);
      assert s11.Peek(0) == 0x5e3;
      assert s11.Peek(4) == 0x163;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s12, gas - 1)
      else
        ExecuteFromCFGNode_s23(s12, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 104
    * Starting at 0x5d6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Address(s8);
      var s10 := Eq(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s24(s10, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 105
    * Starting at 0x5e3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x163;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x060c);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s4, gas - 1)
      else
        ExecuteFromCFGNode_s25(s4, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 106
    * Starting at 0x5e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x163;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0xcb9339d5);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(4) == 0x163;
      var s12 := Sub(s11);
      var s13 := Dup3(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x04);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x24);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x02fe);
      assert s21.Peek(0) == 0x2fe;
      assert s21.Peek(3) == 0x163;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s22, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x163;
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

  /** Node 27
    * Segment Id for this node is: 107
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x03);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Not(s9);
      var s11 := And(s10);
      assert s11.Peek(3) == 0x163;
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
      assert s21.Peek(3) == 0x163;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := Or(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s27, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 32
    * Starting at 0x163
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163 as nat
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

  /** Node 29
    * Segment Id for this node is: 58
    * Starting at 0x277
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x277 as nat
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
      var s5 := Push2(s4, 0x0283);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s6, gas - 1)
      else
        ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 59
    * Starting at 0x27f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27f as nat
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

  /** Node 31
    * Segment Id for this node is: 60
    * Starting at 0x283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0163);
      var s4 := Push2(s3, 0x0292);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0ae1);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s8, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 158
    * Starting at 0xae1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x292

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(3) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0af3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s10, gas - 1)
      else
        ExecuteFromCFGNode_s33(s10, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 159
    * Starting at 0xaef
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x292

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x292;
      assert s1.Peek(5) == 0x163;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 34
    * Segment Id for this node is: 160
    * Starting at 0xaf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x292

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x292;
      assert s1.Peek(4) == 0x163;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x292;
      assert s11.Peek(7) == 0x163;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b0a);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s14, gas - 1)
      else
        ExecuteFromCFGNode_s35(s14, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 161
    * Starting at 0xb06
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x292

    requires s0.stack[5] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x292;
      assert s1.Peek(6) == 0x163;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 36
    * Segment Id for this node is: 162
    * Starting at 0xb0a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x292

    requires s0.stack[5] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x292;
      assert s1.Peek(5) == 0x163;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s7, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 61
    * Starting at 0x292
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x0544);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s3, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 97
    * Starting at 0x544
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x544 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x054c);
      var s3 := Push2(s2, 0x062e);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s4, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 108
    * Starting at 0x62e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x54c

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x54c;
      assert s1.Peek(2) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x54c;
      assert s11.Peek(3) == 0x163;
      var s12 := Push2(s11, 0x031e);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s13, gas - 1)
      else
        ExecuteFromCFGNode_s40(s13, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 109
    * Starting at 0x641
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x641 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x54c

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x54c;
      assert s1.Peek(3) == 0x163;
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
      assert s11.Peek(3) == 0x54c;
      assert s11.Peek(5) == 0x163;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x54c;
      assert s21.Peek(6) == 0x163;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x02fe);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s27, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x54c

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x54c;
      assert s1.Peek(3) == 0x163;
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

  /** Node 42
    * Segment Id for this node is: 73
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x54c

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x54c;
      assert s1.Peek(2) == 0x163;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s2, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 98
    * Starting at 0x54c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x05b1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s10, gas - 1)
      else
        ExecuteFromCFGNode_s44(s10, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 99
    * Starting at 0x55b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x163;
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
      assert s11.Peek(4) == 0x163;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x163;
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
      assert s31.Peek(2) == 0x163;
      var s32 := Push2(s31, 0x02fe);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s33, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 100
    * Starting at 0x5b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x05ba);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0688);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s5, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 110
    * Starting at 0x688
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x688 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5ba

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5ba;
      assert s1.Peek(3) == 0x163;
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
      assert s11.Peek(6) == 0x5ba;
      assert s11.Peek(8) == 0x163;
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
      assert s21.Peek(7) == 0x5ba;
      assert s21.Peek(9) == 0x163;
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
      assert s31.Peek(5) == 0x5ba;
      assert s31.Peek(7) == 0x163;
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
      ExecuteFromCFGNode_s47(s40, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 101
    * Starting at 0x5ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s3, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 55
    * Starting at 0x261
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x261 as nat
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
      var s5 := Push2(s4, 0x026d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s6, gas - 1)
      else
        ExecuteFromCFGNode_s49(s6, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 56
    * Starting at 0x269
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x269 as nat
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

  /** Node 50
    * Segment Id for this node is: 57
    * Starting at 0x26d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0233);
      var s4 := Push1(s3, 0x04);
      var s5 := SLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s7, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 50
    * Starting at 0x233
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x233 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x233

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x233;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x00fb);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s10, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 23
    * Starting at 0xfb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x233

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x233;
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
    * Segment Id for this node is: 51
    * Starting at 0x241
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x241 as nat
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
      var s5 := Push2(s4, 0x024d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s6, gas - 1)
      else
        ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 52
    * Starting at 0x249
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x249 as nat
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

  /** Node 55
    * Segment Id for this node is: 53
    * Starting at 0x24d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0163);
      var s4 := Push2(s3, 0x025c);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0ae1);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s8, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 158
    * Starting at 0xae1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x25c

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x25c;
      assert s1.Peek(3) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0af3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s10, gas - 1)
      else
        ExecuteFromCFGNode_s57(s10, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 159
    * Starting at 0xaef
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x25c

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x25c;
      assert s1.Peek(5) == 0x163;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 58
    * Segment Id for this node is: 160
    * Starting at 0xaf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x25c

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x25c;
      assert s1.Peek(4) == 0x163;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x25c;
      assert s11.Peek(7) == 0x163;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b0a);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s14, gas - 1)
      else
        ExecuteFromCFGNode_s59(s14, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 161
    * Starting at 0xb06
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x25c

    requires s0.stack[5] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x25c;
      assert s1.Peek(6) == 0x163;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 60
    * Segment Id for this node is: 162
    * Starting at 0xb0a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x25c

    requires s0.stack[5] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x25c;
      assert s1.Peek(5) == 0x163;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s7, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 54
    * Starting at 0x25c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x0496);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s3, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 90
    * Starting at 0x496
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x496 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x049e);
      var s3 := Push2(s2, 0x062e);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s4, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 108
    * Starting at 0x62e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x49e

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x49e;
      assert s1.Peek(2) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x49e;
      assert s11.Peek(3) == 0x163;
      var s12 := Push2(s11, 0x031e);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s13, gas - 1)
      else
        ExecuteFromCFGNode_s64(s13, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 109
    * Starting at 0x641
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x641 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x49e

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x49e;
      assert s1.Peek(3) == 0x163;
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
      assert s11.Peek(3) == 0x49e;
      assert s11.Peek(5) == 0x163;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x49e;
      assert s21.Peek(6) == 0x163;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x02fe);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s27, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x49e

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x49e;
      assert s1.Peek(3) == 0x163;
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

  /** Node 66
    * Segment Id for this node is: 73
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x49e

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x49e;
      assert s1.Peek(2) == 0x163;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s2, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 91
    * Starting at 0x49e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := IsZero(s8);
      var s10 := Dup1(s9);
      var s11 := Push2(s10, 0x04bc);
      assert s11.Peek(0) == 0x4bc;
      assert s11.Peek(4) == 0x163;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s12, gas - 1)
      else
        ExecuteFromCFGNode_s68(s12, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 92
    * Starting at 0x4af
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Address(s8);
      var s10 := Eq(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s69(s10, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 93
    * Starting at 0x4bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x163;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x04e5);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s4, gas - 1)
      else
        ExecuteFromCFGNode_s70(s4, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 94
    * Starting at 0x4c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x163;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x0c760937);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(4) == 0x163;
      var s12 := Sub(s11);
      var s13 := Dup3(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x04);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x24);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x02fe);
      assert s21.Peek(0) == 0x2fe;
      assert s21.Peek(3) == 0x163;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s22, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 95
    * Starting at 0x4e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x02);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Not(s9);
      var s11 := And(s10);
      assert s11.Peek(3) == 0x163;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup4(s16);
      var s18 := And(s17);
      var s19 := Or(s18);
      var s20 := Dup1(s19);
      var s21 := Dup3(s20);
      assert s21.Peek(5) == 0x163;
      var s22 := SStore(s21);
      var s23 := Push1(s22, 0x14);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x051d);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x01);
      var s28 := Push1(s27, 0xa0);
      var s29 := Shl(s28);
      var s30 := Swap1(s29);
      var s31 := Div(s30);
      assert s31.Peek(1) == 0x51d;
      assert s31.Peek(5) == 0x163;
      var s32 := Push1(s31, 0x01);
      var s33 := Push1(s32, 0x01);
      var s34 := Push1(s33, 0x60);
      var s35 := Shl(s34);
      var s36 := Sub(s35);
      var s37 := And(s36);
      var s38 := Push2(s37, 0x0c2f);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s39, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 176
    * Starting at 0xc2f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x51d

    requires s0.stack[5] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x51d;
      assert s1.Peek(5) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x60);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup1(s7);
      var s9 := Dup4(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x51d;
      assert s11.Peek(9) == 0x163;
      var s12 := Dup2(s11);
      var s13 := Sub(s12);
      var s14 := Push2(s13, 0x0c4b);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s15, gas - 1)
      else
        ExecuteFromCFGNode_s73(s15, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 177
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x51d

    requires s0.stack[8] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0c4b);
      assert s1.Peek(0) == 0xc4b;
      assert s1.Peek(5) == 0x51d;
      assert s1.Peek(9) == 0x163;
      var s2 := Push2(s1, 0x0c19);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s3, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 175
    * Starting at 0xc19
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0xc4b

    requires s0.stack[5] == 0x51d

    requires s0.stack[9] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc4b;
      assert s1.Peek(5) == 0x51d;
      assert s1.Peek(9) == 0x163;
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
      assert s11.Peek(2) == 0xc4b;
      assert s11.Peek(7) == 0x51d;
      assert s11.Peek(11) == 0x163;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 75
    * Segment Id for this node is: 178
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x51d

    requires s0.stack[8] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x51d;
      assert s1.Peek(8) == 0x163;
      var s2 := Push1(s1, 0x01);
      var s3 := Add(s2);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s9, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 96
    * Starting at 0x51d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x163;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Exp(s4);
      var s6 := Dup2(s5);
      var s7 := SLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x60);
      assert s11.Peek(9) == 0x163;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := Mul(s13);
      var s15 := Not(s14);
      var s16 := And(s15);
      var s17 := Swap1(s16);
      var s18 := Dup4(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0x60);
      assert s21.Peek(9) == 0x163;
      var s22 := Shl(s21);
      var s23 := Sub(s22);
      var s24 := And(s23);
      var s25 := Mul(s24);
      var s26 := Or(s25);
      var s27 := Swap1(s26);
      var s28 := SStore(s27);
      var s29 := Pop(s28);
      var s30 := Pop(s29);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s31, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 8
    * Starting at 0x59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x831e80f2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x01ce);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s6, gas - 1)
      else
        ExecuteFromCFGNode_s78(s6, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 9
    * Starting at 0x65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01e1);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s5, gas - 1)
      else
        ExecuteFromCFGNode_s79(s5, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 10
    * Starting at 0x70
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xbc063e1a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ff);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s5, gas - 1)
      else
        ExecuteFromCFGNode_s80(s5, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 11
    * Starting at 0x7b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
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

  /** Node 81
    * Segment Id for this node is: 47
    * Starting at 0x1ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ff as nat
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
      var s5 := Push2(s4, 0x020b);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s6, gas - 1)
      else
        ExecuteFromCFGNode_s82(s6, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 48
    * Starting at 0x207
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x207 as nat
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

  /** Node 83
    * Segment Id for this node is: 49
    * Starting at 0x20b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0233);
      var s4 := Push32(s3, 0x00000000000000000000000000000000000000000052b7d2dcc80cd2e4000000);
      var s5 := Dup2(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s6, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 44
    * Starting at 0x1e1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e1 as nat
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
      var s5 := Push2(s4, 0x01ed);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s6, gas - 1)
      else
        ExecuteFromCFGNode_s85(s6, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 45
    * Starting at 0x1e9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e9 as nat
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

  /** Node 86
    * Segment Id for this node is: 46
    * Starting at 0x1ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ed as nat
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
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Push2(s10, 0x00e7);
      assert s11.Peek(0) == 0xe7;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s12, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 22
    * Starting at 0xe7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7 as nat
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
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s88(s15, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 23
    * Starting at 0xfb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb as nat
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

  /** Node 89
    * Segment Id for this node is: 42
    * Starting at 0x1ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e7);
      var s3 := Push2(s2, 0x01dc);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0a5d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s7, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 147
    * Starting at 0xa5d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1dc

    requires s0.stack[3] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1dc;
      assert s1.Peek(3) == 0xe7;
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
      assert s11.Peek(7) == 0x1dc;
      assert s11.Peek(8) == 0xe7;
      var s12 := Push2(s11, 0x0a73);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s13, gas - 1)
      else
        ExecuteFromCFGNode_s91(s13, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 148
    * Starting at 0xa6f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1dc

    requires s0.stack[7] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x1dc;
      assert s1.Peek(8) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 92
    * Segment Id for this node is: 149
    * Starting at 0xa73
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1dc

    requires s0.stack[7] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1dc;
      assert s1.Peek(7) == 0xe7;
      var s2 := Dup5(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0a8b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s10, gas - 1)
      else
        ExecuteFromCFGNode_s93(s10, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 150
    * Starting at 0xa87
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x1dc

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(9) == 0x1dc;
      assert s1.Peek(10) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 94
    * Segment Id for this node is: 151
    * Starting at 0xa8b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x1dc

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1dc;
      assert s1.Peek(9) == 0xe7;
      var s2 := Push2(s1, 0x0a97);
      var s3 := Dup9(s2);
      var s4 := Dup4(s3);
      var s5 := Dup10(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x09d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s8, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 138
    * Starting at 0x9d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xa97

    requires s0.stack[11] == 0x1dc

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa97;
      assert s1.Peek(11) == 0x1dc;
      assert s1.Peek(12) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x09e1);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s9, gas - 1)
      else
        ExecuteFromCFGNode_s96(s9, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 139
    * Starting at 0x9dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa97

    requires s0.stack[12] == 0x1dc

    requires s0.stack[13] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xa97;
      assert s1.Peek(13) == 0x1dc;
      assert s1.Peek(14) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 97
    * Segment Id for this node is: 140
    * Starting at 0x9e1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa97

    requires s0.stack[12] == 0x1dc

    requires s0.stack[13] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa97;
      assert s1.Peek(12) == 0x1dc;
      assert s1.Peek(13) == 0xe7;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x09fc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s10, gas - 1)
      else
        ExecuteFromCFGNode_s98(s10, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 141
    * Starting at 0x9f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xa97

    requires s0.stack[14] == 0x1dc

    requires s0.stack[15] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09fc);
      assert s1.Peek(0) == 0x9fc;
      assert s1.Peek(6) == 0xa97;
      assert s1.Peek(15) == 0x1dc;
      assert s1.Peek(16) == 0xe7;
      var s2 := Push2(s1, 0x09ba);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s3, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 137
    * Starting at 0x9ba
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x9fc

    requires s0.stack[6] == 0xa97

    requires s0.stack[15] == 0x1dc

    requires s0.stack[16] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9fc;
      assert s1.Peek(6) == 0xa97;
      assert s1.Peek(15) == 0x1dc;
      assert s1.Peek(16) == 0xe7;
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
      assert s11.Peek(2) == 0x9fc;
      assert s11.Peek(8) == 0xa97;
      assert s11.Peek(17) == 0x1dc;
      assert s11.Peek(18) == 0xe7;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 100
    * Segment Id for this node is: 142
    * Starting at 0x9fc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xa97

    requires s0.stack[14] == 0x1dc

    requires s0.stack[15] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa97;
      assert s1.Peek(14) == 0x1dc;
      assert s1.Peek(15) == 0xe7;
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
      assert s11.Peek(8) == 0xa97;
      assert s11.Peek(17) == 0x1dc;
      assert s11.Peek(18) == 0xe7;
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
      assert s21.Peek(9) == 0xa97;
      assert s21.Peek(18) == 0x1dc;
      assert s21.Peek(19) == 0xe7;
      var s22 := Dup4(s21);
      var s23 := Lt(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := Push2(s25, 0x0a24);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s27, gas - 1)
      else
        ExecuteFromCFGNode_s101(s27, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 143
    * Starting at 0xa1d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0xa97

    requires s0.stack[16] == 0x1dc

    requires s0.stack[17] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a24);
      assert s1.Peek(0) == 0xa24;
      assert s1.Peek(8) == 0xa97;
      assert s1.Peek(17) == 0x1dc;
      assert s1.Peek(18) == 0xe7;
      var s2 := Push2(s1, 0x09ba);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s3, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 137
    * Starting at 0x9ba
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xa24

    requires s0.stack[8] == 0xa97

    requires s0.stack[17] == 0x1dc

    requires s0.stack[18] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa24;
      assert s1.Peek(8) == 0xa97;
      assert s1.Peek(17) == 0x1dc;
      assert s1.Peek(18) == 0xe7;
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
      assert s11.Peek(2) == 0xa24;
      assert s11.Peek(10) == 0xa97;
      assert s11.Peek(19) == 0x1dc;
      assert s11.Peek(20) == 0xe7;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 103
    * Segment Id for this node is: 144
    * Starting at 0xa24
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0xa97

    requires s0.stack[16] == 0x1dc

    requires s0.stack[17] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xa97;
      assert s1.Peek(16) == 0x1dc;
      assert s1.Peek(17) == 0xe7;
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
      assert s11.Peek(11) == 0xa97;
      assert s11.Peek(20) == 0x1dc;
      assert s11.Peek(21) == 0xe7;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0a3d);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s17, gas - 1)
      else
        ExecuteFromCFGNode_s104(s17, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 145
    * Starting at 0xa39
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0xa97

    requires s0.stack[16] == 0x1dc

    requires s0.stack[17] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0xa97;
      assert s1.Peek(17) == 0x1dc;
      assert s1.Peek(18) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 105
    * Segment Id for this node is: 146
    * Starting at 0xa3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0xa97

    requires s0.stack[16] == 0x1dc

    requires s0.stack[17] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xa97;
      assert s1.Peek(16) == 0x1dc;
      assert s1.Peek(17) == 0xe7;
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
      assert s11.Peek(9) == 0xa97;
      assert s11.Peek(18) == 0x1dc;
      assert s11.Peek(19) == 0xe7;
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
      assert s21.Peek(5) == 0xa97;
      assert s21.Peek(14) == 0x1dc;
      assert s21.Peek(15) == 0xe7;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s28, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 152
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x1dc

    requires s0.stack[10] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x1dc;
      assert s1.Peek(10) == 0xe7;
      var s2 := Swap6(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Dup1(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(10) == 0x1dc;
      assert s11.Peek(11) == 0xe7;
      var s12 := Gt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x0aad);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s15, gas - 1)
      else
        ExecuteFromCFGNode_s107(s15, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 153
    * Starting at 0xaa9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x1dc

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(9) == 0x1dc;
      assert s1.Peek(10) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 108
    * Segment Id for this node is: 154
    * Starting at 0xaad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x1dc

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1dc;
      assert s1.Peek(9) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0aba);
      var s4 := Dup8(s3);
      var s5 := Dup3(s4);
      var s6 := Dup9(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x09d0);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s9, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 138
    * Starting at 0x9d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xaba

    requires s0.stack[10] == 0x1dc

    requires s0.stack[11] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaba;
      assert s1.Peek(10) == 0x1dc;
      assert s1.Peek(11) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x09e1);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s9, gas - 1)
      else
        ExecuteFromCFGNode_s110(s9, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 139
    * Starting at 0x9dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaba

    requires s0.stack[11] == 0x1dc

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xaba;
      assert s1.Peek(12) == 0x1dc;
      assert s1.Peek(13) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 111
    * Segment Id for this node is: 140
    * Starting at 0x9e1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaba

    requires s0.stack[11] == 0x1dc

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaba;
      assert s1.Peek(11) == 0x1dc;
      assert s1.Peek(12) == 0xe7;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x09fc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s10, gas - 1)
      else
        ExecuteFromCFGNode_s112(s10, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 141
    * Starting at 0x9f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaba

    requires s0.stack[13] == 0x1dc

    requires s0.stack[14] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09fc);
      assert s1.Peek(0) == 0x9fc;
      assert s1.Peek(6) == 0xaba;
      assert s1.Peek(14) == 0x1dc;
      assert s1.Peek(15) == 0xe7;
      var s2 := Push2(s1, 0x09ba);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s3, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 137
    * Starting at 0x9ba
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x9fc

    requires s0.stack[6] == 0xaba

    requires s0.stack[14] == 0x1dc

    requires s0.stack[15] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9fc;
      assert s1.Peek(6) == 0xaba;
      assert s1.Peek(14) == 0x1dc;
      assert s1.Peek(15) == 0xe7;
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
      assert s11.Peek(2) == 0x9fc;
      assert s11.Peek(8) == 0xaba;
      assert s11.Peek(16) == 0x1dc;
      assert s11.Peek(17) == 0xe7;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 114
    * Segment Id for this node is: 142
    * Starting at 0x9fc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaba

    requires s0.stack[13] == 0x1dc

    requires s0.stack[14] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaba;
      assert s1.Peek(13) == 0x1dc;
      assert s1.Peek(14) == 0xe7;
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
      assert s11.Peek(8) == 0xaba;
      assert s11.Peek(16) == 0x1dc;
      assert s11.Peek(17) == 0xe7;
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
      assert s21.Peek(9) == 0xaba;
      assert s21.Peek(17) == 0x1dc;
      assert s21.Peek(18) == 0xe7;
      var s22 := Dup4(s21);
      var s23 := Lt(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := Push2(s25, 0x0a24);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s27, gas - 1)
      else
        ExecuteFromCFGNode_s115(s27, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 143
    * Starting at 0xa1d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0xaba

    requires s0.stack[15] == 0x1dc

    requires s0.stack[16] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a24);
      assert s1.Peek(0) == 0xa24;
      assert s1.Peek(8) == 0xaba;
      assert s1.Peek(16) == 0x1dc;
      assert s1.Peek(17) == 0xe7;
      var s2 := Push2(s1, 0x09ba);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s3, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 137
    * Starting at 0x9ba
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xa24

    requires s0.stack[8] == 0xaba

    requires s0.stack[16] == 0x1dc

    requires s0.stack[17] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa24;
      assert s1.Peek(8) == 0xaba;
      assert s1.Peek(16) == 0x1dc;
      assert s1.Peek(17) == 0xe7;
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
      assert s11.Peek(2) == 0xa24;
      assert s11.Peek(10) == 0xaba;
      assert s11.Peek(18) == 0x1dc;
      assert s11.Peek(19) == 0xe7;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 117
    * Segment Id for this node is: 144
    * Starting at 0xa24
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0xaba

    requires s0.stack[15] == 0x1dc

    requires s0.stack[16] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xaba;
      assert s1.Peek(15) == 0x1dc;
      assert s1.Peek(16) == 0xe7;
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
      assert s11.Peek(11) == 0xaba;
      assert s11.Peek(19) == 0x1dc;
      assert s11.Peek(20) == 0xe7;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0a3d);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s119(s17, gas - 1)
      else
        ExecuteFromCFGNode_s118(s17, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 145
    * Starting at 0xa39
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0xaba

    requires s0.stack[15] == 0x1dc

    requires s0.stack[16] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0xaba;
      assert s1.Peek(16) == 0x1dc;
      assert s1.Peek(17) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 119
    * Segment Id for this node is: 146
    * Starting at 0xa3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0xaba

    requires s0.stack[15] == 0x1dc

    requires s0.stack[16] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xaba;
      assert s1.Peek(15) == 0x1dc;
      assert s1.Peek(16) == 0xe7;
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
      assert s11.Peek(9) == 0xaba;
      assert s11.Peek(17) == 0x1dc;
      assert s11.Peek(18) == 0xe7;
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
      assert s21.Peek(5) == 0xaba;
      assert s21.Peek(13) == 0x1dc;
      assert s21.Peek(14) == 0xe7;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s28, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 155
    * Starting at 0xaba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x1dc

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1dc;
      assert s1.Peek(9) == 0xe7;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push1(s8, 0xff);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x1dc;
      assert s11.Peek(9) == 0xe7;
      var s12 := Dup2(s11);
      var s13 := Eq(s12);
      var s14 := Push2(s13, 0x0ad1);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s122(s15, gas - 1)
      else
        ExecuteFromCFGNode_s121(s15, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 156
    * Starting at 0xacd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xacd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x1dc

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x1dc;
      assert s1.Peek(9) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 122
    * Segment Id for this node is: 157
    * Starting at 0xad1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x1dc

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1dc;
      assert s1.Peek(8) == 0xe7;
      var s2 := Swap4(s1);
      var s3 := Swap7(s2);
      var s4 := Swap3(s3);
      var s5 := Swap6(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap4(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Add(s9);
      var s11 := CallDataLoad(s10);
      assert s11.Peek(2) == 0x1dc;
      assert s11.Peek(7) == 0xe7;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s15, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 43
    * Starting at 0x1dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe7;
      var s2 := Push2(s1, 0x0320);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s3, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 74
    * Starting at 0x320
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x320 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x04);
      var s4 := SLoad(s3);
      var s5 := CallValue(s4);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0347);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s9, gas - 1)
      else
        ExecuteFromCFGNode_s125(s9, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 75
    * Starting at 0x32d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0xe7;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x131398d7);
      var s4 := Push1(s3, 0xe2);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := CallValue(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0xe7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x02fe);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s16, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xe7;
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
    * Segment Id for this node is: 76
    * Starting at 0x347
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x347 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe7;
      var s2 := Push2(s1, 0x034f);
      var s3 := Push2(s2, 0x06d8);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s4, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 111
    * Starting at 0x6d8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x34f

    requires s0.stack[6] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(6) == 0xe7;
      var s2 := Push1(s1, 0x02);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x072a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s7, gas - 1)
      else
        ExecuteFromCFGNode_s129(s7, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 112
    * Starting at 0x6e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x34f

    requires s0.stack[6] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x34f;
      assert s1.Peek(7) == 0xe7;
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
      assert s11.Peek(3) == 0x34f;
      assert s11.Peek(9) == 0xe7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5265656e7472616e637947756172643a207265656e7472616e742063616c6c00);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x34f;
      assert s21.Peek(9) == 0xe7;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x02fe);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s26, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x34f

    requires s0.stack[7] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x34f;
      assert s1.Peek(7) == 0xe7;
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

  /** Node 131
    * Segment Id for this node is: 113
    * Starting at 0x72a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x34f

    requires s0.stack[6] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(6) == 0xe7;
      var s2 := Push1(s1, 0x02);
      var s3 := Push1(s2, 0x01);
      var s4 := SStore(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s5, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 77
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe7;
      var s2 := Push2(s1, 0x0357);
      var s3 := Push2(s2, 0x0731);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s4, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 114
    * Starting at 0x731
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x731 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x357

    requires s0.stack[6] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x357;
      assert s1.Peek(6) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x04);
      var s4 := SLoad(s3);
      var s5 := CallValue(s4);
      var s6 := Push2(s5, 0x0741);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x0c55);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s10, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 179
    * Starting at 0xc55
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x741

    requires s0.stack[4] == 0x357

    requires s0.stack[10] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x741;
      assert s1.Peek(4) == 0x357;
      assert s1.Peek(10) == 0xe7;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x090a);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s10, gas - 1)
      else
        ExecuteFromCFGNode_s135(s10, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 180
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x741

    requires s0.stack[5] == 0x357

    requires s0.stack[11] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x090a);
      assert s1.Peek(0) == 0x90a;
      assert s1.Peek(4) == 0x741;
      assert s1.Peek(6) == 0x357;
      assert s1.Peek(12) == 0xe7;
      var s2 := Push2(s1, 0x0c19);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s3, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 175
    * Starting at 0xc19
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x90a

    requires s0.stack[4] == 0x741

    requires s0.stack[6] == 0x357

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x90a;
      assert s1.Peek(4) == 0x741;
      assert s1.Peek(6) == 0x357;
      assert s1.Peek(12) == 0xe7;
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
      assert s11.Peek(2) == 0x90a;
      assert s11.Peek(6) == 0x741;
      assert s11.Peek(8) == 0x357;
      assert s11.Peek(14) == 0xe7;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 137
    * Segment Id for this node is: 127
    * Starting at 0x90a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x741

    requires s0.stack[5] == 0x357

    requires s0.stack[11] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x741;
      assert s1.Peek(5) == 0x357;
      assert s1.Peek(11) == 0xe7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s6, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 115
    * Starting at 0x741
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x741 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x357

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x357;
      assert s1.Peek(8) == 0xe7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x05ba);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s7, gas - 1)
      else
        ExecuteFromCFGNode_s139(s7, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 116
    * Starting at 0x74a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x357

    requires s0.stack[7] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05ba);
      assert s1.Peek(0) == 0x5ba;
      assert s1.Peek(2) == 0x357;
      assert s1.Peek(8) == 0xe7;
      var s2 := Caller(s1);
      var s3 := Dup3(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s140(s3, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 117
    * Starting at 0x74f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x5ba

    requires s0.stack[4] == 0x357

    requires s0.stack[10] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5ba;
      assert s1.Peek(4) == 0x357;
      assert s1.Peek(10) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := SelfBalance(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x079f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s7, gas - 1)
      else
        ExecuteFromCFGNode_s141(s7, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 118
    * Starting at 0x758
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x758 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x5ba

    requires s0.stack[4] == 0x357

    requires s0.stack[10] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x5ba;
      assert s1.Peek(5) == 0x357;
      assert s1.Peek(11) == 0xe7;
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
      assert s11.Peek(5) == 0x5ba;
      assert s11.Peek(7) == 0x357;
      assert s11.Peek(13) == 0xe7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20696e73756666696369656e742062616c616e6365000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x5ba;
      assert s21.Peek(7) == 0x357;
      assert s21.Peek(13) == 0xe7;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x02fe);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s26, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x5ba

    requires s0.stack[5] == 0x357

    requires s0.stack[11] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ba;
      assert s1.Peek(5) == 0x357;
      assert s1.Peek(11) == 0xe7;
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

  /** Node 143
    * Segment Id for this node is: 119
    * Starting at 0x79f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x5ba

    requires s0.stack[4] == 0x357

    requires s0.stack[10] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5ba;
      assert s1.Peek(4) == 0x357;
      assert s1.Peek(10) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Dup3(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(6) == 0x5ba;
      assert s11.Peek(8) == 0x357;
      assert s11.Peek(14) == 0xe7;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x00);
      var s14 := Push1(s13, 0x40);
      var s15 := MLoad(s14);
      var s16 := Dup1(s15);
      var s17 := Dup4(s16);
      var s18 := Sub(s17);
      var s19 := Dup2(s18);
      var s20 := Dup6(s19);
      var s21 := Dup8(s20);
      assert s21.Peek(12) == 0x5ba;
      assert s21.Peek(14) == 0x357;
      assert s21.Peek(20) == 0xe7;
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := Swap3(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := ReturnDataSize(s27);
      var s29 := Dup1(s28);
      var s30 := Push1(s29, 0x00);
      var s31 := Dup2(s30);
      assert s31.Peek(8) == 0x5ba;
      assert s31.Peek(10) == 0x357;
      assert s31.Peek(16) == 0xe7;
      var s32 := Eq(s31);
      var s33 := Push2(s32, 0x07ec);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s208(s34, gas - 1)
      else
        ExecuteFromCFGNode_s144(s34, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 120
    * Starting at 0x7cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x5ba

    requires s0.stack[8] == 0x357

    requires s0.stack[14] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(7) == 0x5ba;
      assert s1.Peek(9) == 0x357;
      assert s1.Peek(15) == 0xe7;
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
      assert s11.Peek(8) == 0x5ba;
      assert s11.Peek(10) == 0x357;
      assert s11.Peek(16) == 0xe7;
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
      assert s21.Peek(10) == 0x5ba;
      assert s21.Peek(12) == 0x357;
      assert s21.Peek(18) == 0xe7;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x07f1);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s25, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 122
    * Starting at 0x7f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x5ba

    requires s0.stack[8] == 0x357

    requires s0.stack[14] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x5ba;
      assert s1.Peek(8) == 0x357;
      assert s1.Peek(14) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x0868);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s8, gas - 1)
      else
        ExecuteFromCFGNode_s146(s8, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 123
    * Starting at 0x7fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x5ba

    requires s0.stack[5] == 0x357

    requires s0.stack[11] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5ba;
      assert s1.Peek(6) == 0x357;
      assert s1.Peek(12) == 0xe7;
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
      assert s11.Peek(6) == 0x5ba;
      assert s11.Peek(8) == 0x357;
      assert s11.Peek(14) == 0xe7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x3a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20756e61626c6520746f2073656e642076616c75652c2072);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x5ba;
      assert s21.Peek(8) == 0x357;
      assert s21.Peek(14) == 0xe7;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6563697069656e74206d61792068617665207265766572746564000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x02fe);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s31, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x5ba

    requires s0.stack[6] == 0x357

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5ba;
      assert s1.Peek(6) == 0x357;
      assert s1.Peek(12) == 0xe7;
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

  /** Node 148
    * Segment Id for this node is: 124
    * Starting at 0x868
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x868 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x5ba

    requires s0.stack[5] == 0x357

    requires s0.stack[11] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ba;
      assert s1.Peek(5) == 0x357;
      assert s1.Peek(11) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s5, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 101
    * Starting at 0x5ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x357

    requires s0.stack[7] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x357;
      assert s1.Peek(7) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s3, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 78
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe7;
      var s2 := Push1(s1, 0x04);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x03);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0372);
      var s7 := Swap2(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(4) == 0x372;
      assert s11.Peek(10) == 0xe7;
      var s12 := Sub(s11);
      var s13 := Swap1(s12);
      var s14 := Swap2(s13);
      var s15 := And(s14);
      var s16 := Swap1(s15);
      var s17 := Push2(s16, 0x074f);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s18, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 117
    * Starting at 0x74f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x372

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x372;
      assert s1.Peek(8) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := SelfBalance(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x079f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s7, gas - 1)
      else
        ExecuteFromCFGNode_s152(s7, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 118
    * Starting at 0x758
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x758 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x372

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(9) == 0xe7;
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
      assert s11.Peek(5) == 0x372;
      assert s11.Peek(11) == 0xe7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20696e73756666696369656e742062616c616e6365000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x372;
      assert s21.Peek(11) == 0xe7;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x02fe);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s26, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x372

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(9) == 0xe7;
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

  /** Node 154
    * Segment Id for this node is: 119
    * Starting at 0x79f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x372

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x372;
      assert s1.Peek(8) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Dup3(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(12) == 0xe7;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x00);
      var s14 := Push1(s13, 0x40);
      var s15 := MLoad(s14);
      var s16 := Dup1(s15);
      var s17 := Dup4(s16);
      var s18 := Sub(s17);
      var s19 := Dup2(s18);
      var s20 := Dup6(s19);
      var s21 := Dup8(s20);
      assert s21.Peek(12) == 0x372;
      assert s21.Peek(18) == 0xe7;
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := Swap3(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := ReturnDataSize(s27);
      var s29 := Dup1(s28);
      var s30 := Push1(s29, 0x00);
      var s31 := Dup2(s30);
      assert s31.Peek(8) == 0x372;
      assert s31.Peek(14) == 0xe7;
      var s32 := Eq(s31);
      var s33 := Push2(s32, 0x07ec);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s34, gas - 1)
      else
        ExecuteFromCFGNode_s155(s34, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 120
    * Starting at 0x7cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x372

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(7) == 0x372;
      assert s1.Peek(13) == 0xe7;
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
      assert s11.Peek(8) == 0x372;
      assert s11.Peek(14) == 0xe7;
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
      assert s21.Peek(10) == 0x372;
      assert s21.Peek(16) == 0xe7;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x07f1);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s25, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 122
    * Starting at 0x7f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x372

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x372;
      assert s1.Peek(12) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x0868);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s8, gas - 1)
      else
        ExecuteFromCFGNode_s157(s8, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 123
    * Starting at 0x7fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x372

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(10) == 0xe7;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(12) == 0xe7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x3a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20756e61626c6520746f2073656e642076616c75652c2072);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x372;
      assert s21.Peek(12) == 0xe7;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6563697069656e74206d61792068617665207265766572746564000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x02fe);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s31, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x372

    requires s0.stack[10] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(10) == 0xe7;
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

  /** Node 159
    * Segment Id for this node is: 124
    * Starting at 0x868
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x868 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x372

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(9) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s5, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 79
    * Starting at 0x372
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x372 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe7;
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push2(s5, 0x03b7);
      var s7 := Swap2(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(4) == 0x3b7;
      assert s11.Peek(10) == 0xe7;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x039c);
      var s16 := Swap1(s15);
      var s17 := Caller(s16);
      var s18 := Swap1(s17);
      var s19 := Dup10(s18);
      var s20 := Swap1(s19);
      var s21 := Dup10(s20);
      assert s21.Peek(4) == 0x39c;
      assert s21.Peek(6) == 0x3b7;
      assert s21.Peek(12) == 0xe7;
      var s22 := Swap1(s21);
      var s23 := Dup10(s22);
      var s24 := Swap1(s23);
      var s25 := Dup10(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Push2(s28, 0x0b35);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s30, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 167
    * Starting at 0xb35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x39c

    requires s0.stack[8] == 0x3b7

    requires s0.stack[14] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x39c;
      assert s1.Peek(8) == 0x3b7;
      assert s1.Peek(14) == 0xe7;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x60);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Not(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Shl(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x39c;
      assert s11.Peek(9) == 0x3b7;
      assert s11.Peek(15) == 0xe7;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup6(s14);
      var s16 := MLoad(s15);
      var s17 := Push2(s16, 0x0b5a);
      var s18 := Dup2(s17);
      var s19 := Push1(s18, 0x14);
      var s20 := Dup6(s19);
      var s21 := Add(s20);
      assert s21.Peek(2) == 0xb5a;
      assert s21.Peek(11) == 0x39c;
      assert s21.Peek(13) == 0x3b7;
      assert s21.Peek(19) == 0xe7;
      var s22 := Push1(s21, 0x20);
      var s23 := Dup11(s22);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x0b11);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s26, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 163
    * Starting at 0xb11
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xb5a

    requires s0.stack[12] == 0x39c

    requires s0.stack[14] == 0x3b7

    requires s0.stack[20] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb5a;
      assert s1.Peek(12) == 0x39c;
      assert s1.Peek(14) == 0x3b7;
      assert s1.Peek(20) == 0xe7;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s163(s2, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 164
    * Starting at 0xb14
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0xb5a

    requires s0.stack[13] == 0x39c

    requires s0.stack[15] == 0x3b7

    requires s0.stack[21] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb5a;
      assert s1.Peek(13) == 0x39c;
      assert s1.Peek(15) == 0x3b7;
      assert s1.Peek(21) == 0xe7;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0b2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s7, gas - 1)
      else
        ExecuteFromCFGNode_s164(s7, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 165
    * Starting at 0xb1d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0xb5a

    requires s0.stack[13] == 0x39c

    requires s0.stack[15] == 0x3b7

    requires s0.stack[21] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0xb5a;
      assert s1.Peek(14) == 0x39c;
      assert s1.Peek(16) == 0x3b7;
      assert s1.Peek(22) == 0xe7;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0b14);
      assert s11.Peek(0) == 0xb14;
      assert s11.Peek(5) == 0xb5a;
      assert s11.Peek(14) == 0x39c;
      assert s11.Peek(16) == 0x3b7;
      assert s11.Peek(22) == 0xe7;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s12, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 166
    * Starting at 0xb2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0xb5a

    requires s0.stack[13] == 0x39c

    requires s0.stack[15] == 0x3b7

    requires s0.stack[21] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb5a;
      assert s1.Peek(13) == 0x39c;
      assert s1.Peek(15) == 0x3b7;
      assert s1.Peek(21) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s8, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 168
    * Starting at 0xb5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x39c

    requires s0.stack[10] == 0x3b7

    requires s0.stack[16] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x39c;
      assert s1.Peek(10) == 0x3b7;
      assert s1.Peek(16) == 0xe7;
      var s2 := Dup6(s1);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0b71);
      var s9 := Dup2(s8);
      var s10 := Push1(s9, 0x14);
      var s11 := Dup5(s10);
      assert s11.Peek(3) == 0xb71;
      assert s11.Peek(13) == 0x39c;
      assert s11.Peek(15) == 0x3b7;
      assert s11.Peek(21) == 0xe7;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup11(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0b11);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s17, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 163
    * Starting at 0xb11
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xb71

    requires s0.stack[13] == 0x39c

    requires s0.stack[15] == 0x3b7

    requires s0.stack[21] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb71;
      assert s1.Peek(13) == 0x39c;
      assert s1.Peek(15) == 0x3b7;
      assert s1.Peek(21) == 0xe7;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s168(s2, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 164
    * Starting at 0xb14
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0xb71

    requires s0.stack[14] == 0x39c

    requires s0.stack[16] == 0x3b7

    requires s0.stack[22] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb71;
      assert s1.Peek(14) == 0x39c;
      assert s1.Peek(16) == 0x3b7;
      assert s1.Peek(22) == 0xe7;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0b2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s7, gas - 1)
      else
        ExecuteFromCFGNode_s169(s7, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 165
    * Starting at 0xb1d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0xb71

    requires s0.stack[14] == 0x39c

    requires s0.stack[16] == 0x3b7

    requires s0.stack[22] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0xb71;
      assert s1.Peek(15) == 0x39c;
      assert s1.Peek(17) == 0x3b7;
      assert s1.Peek(23) == 0xe7;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0b14);
      assert s11.Peek(0) == 0xb14;
      assert s11.Peek(5) == 0xb71;
      assert s11.Peek(15) == 0x39c;
      assert s11.Peek(17) == 0x3b7;
      assert s11.Peek(23) == 0xe7;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s12, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 166
    * Starting at 0xb2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0xb71

    requires s0.stack[14] == 0x39c

    requires s0.stack[16] == 0x3b7

    requires s0.stack[22] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb71;
      assert s1.Peek(14) == 0x39c;
      assert s1.Peek(16) == 0x3b7;
      assert s1.Peek(22) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s8, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 169
    * Starting at 0xb71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[9] == 0x39c

    requires s0.stack[11] == 0x3b7

    requires s0.stack[17] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x39c;
      assert s1.Peek(11) == 0x3b7;
      assert s1.Peek(17) == 0xe7;
      var s2 := Push1(s1, 0xf8);
      var s3 := Swap6(s2);
      var s4 := Swap1(s3);
      var s5 := Swap6(s4);
      var s6 := Shl(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xf8);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(10) == 0x39c;
      assert s11.Peek(12) == 0x3b7;
      assert s11.Peek(18) == 0xe7;
      var s12 := Not(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x14);
      var s15 := Swap2(s14);
      var s16 := Swap1(s15);
      var s17 := Swap6(s16);
      var s18 := Add(s17);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := Add(s20);
      assert s21.Peek(9) == 0x39c;
      assert s21.Peek(11) == 0x3b7;
      assert s21.Peek(17) == 0xe7;
      var s22 := Swap5(s21);
      var s23 := Swap1(s22);
      var s24 := Swap5(s23);
      var s25 := MStore(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Push1(s27, 0x15);
      var s29 := Dup3(s28);
      var s30 := Add(s29);
      var s31 := MStore(s30);
      assert s31.Peek(4) == 0x39c;
      assert s31.Peek(6) == 0x3b7;
      assert s31.Peek(12) == 0xe7;
      var s32 := Push1(s31, 0x35);
      var s33 := Add(s32);
      var s34 := Swap4(s33);
      var s35 := Swap3(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Pop(s37);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s39, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 80
    * Starting at 0x39c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3b7

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3b7;
      assert s1.Peek(8) == 0xe7;
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
      assert s11.Peek(3) == 0x3b7;
      assert s11.Peek(9) == 0xe7;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x086d);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s21, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 125
    * Starting at 0x86d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3b7

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3b7;
      assert s1.Peek(8) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := PushN(s2, 23, 0x3d602d80600a3d3981f3363d3d373d3d3d363d73000000);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Shl(s5);
      var s7 := Push1(s6, 0xe8);
      var s8 := Shr(s7);
      var s9 := Or(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := MStore(s10);
      assert s11.Peek(3) == 0x3b7;
      assert s11.Peek(9) == 0xe7;
      var s12 := PushN(s11, 15, 0x5af43d82803e903d91602b57fd5bf3);
      var s13 := Dup4(s12);
      var s14 := Push1(s13, 0x78);
      var s15 := Shl(s14);
      var s16 := Or(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := MStore(s17);
      var s19 := Dup2(s18);
      var s20 := Push1(s19, 0x37);
      var s21 := Push1(s20, 0x09);
      assert s21.Peek(6) == 0x3b7;
      assert s21.Peek(12) == 0xe7;
      var s22 := Push1(s21, 0x00);
      var s23 := Create2(s22);
      var s24 := Swap1(s23);
      var s25 := Pop(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0x01);
      var s28 := Push1(s27, 0xa0);
      var s29 := Shl(s28);
      var s30 := Sub(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(5) == 0x3b7;
      assert s31.Peek(11) == 0xe7;
      var s32 := And(s31);
      var s33 := Push2(s32, 0x090a);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s34, gas - 1)
      else
        ExecuteFromCFGNode_s174(s34, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 126
    * Starting at 0x8c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3b7

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3b7;
      assert s1.Peek(10) == 0xe7;
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
      assert s11.Peek(6) == 0x3b7;
      assert s11.Peek(12) == 0xe7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x17);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x455243313136373a2063726561746532206661696c6564000000000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x3b7;
      assert s21.Peek(12) == 0xe7;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x02fe);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s26, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3b7

    requires s0.stack[10] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3b7;
      assert s1.Peek(10) == 0xe7;
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

  /** Node 176
    * Segment Id for this node is: 127
    * Starting at 0x90a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3b7

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3b7;
      assert s1.Peek(9) == 0xe7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s6, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 81
    * Starting at 0x3b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xe7;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0xd72bdc53);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Swap1(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(6) == 0xe7;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup3(s16);
      var s18 := And(s17);
      var s19 := Swap1(s18);
      var s20 := Push4(s19, 0xd72bdc53);
      var s21 := Swap1(s20);
      assert s21.Peek(8) == 0xe7;
      var s22 := Push2(s21, 0x03ee);
      var s23 := Swap1(s22);
      var s24 := Caller(s23);
      var s25 := Swap1(s24);
      var s26 := Dup10(s25);
      var s27 := Swap1(s26);
      var s28 := Dup10(s27);
      var s29 := Swap1(s28);
      var s30 := Dup10(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x3ee;
      assert s31.Peek(13) == 0xe7;
      var s32 := Dup10(s31);
      var s33 := Swap1(s32);
      var s34 := Push1(s33, 0x04);
      var s35 := Add(s34);
      var s36 := Push2(s35, 0x0bcb);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s37, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 172
    * Starting at 0xbcb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x3ee

    requires s0.stack[14] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3ee;
      assert s1.Peek(14) == 0xe7;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup7(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(7) == 0x3ee;
      assert s11.Peek(15) == 0xe7;
      var s12 := Push1(s11, 0x20);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x00);
      var s19 := Swap1(s18);
      var s20 := Push2(s19, 0x0bef);
      var s21 := Swap1(s20);
      assert s21.Peek(1) == 0xbef;
      assert s21.Peek(9) == 0x3ee;
      assert s21.Peek(17) == 0xe7;
      var s22 := Dup4(s21);
      var s23 := Add(s22);
      var s24 := Dup8(s23);
      var s25 := Push2(s24, 0x0b9f);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s26, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 170
    * Starting at 0xb9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xbef

    requires s0.stack[10] == 0x3ee

    requires s0.stack[18] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbef;
      assert s1.Peek(10) == 0x3ee;
      assert s1.Peek(18) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push2(s7, 0x0bb7);
      var s9 := Dup2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup7(s10);
      assert s11.Peek(3) == 0xbb7;
      assert s11.Peek(8) == 0xbef;
      assert s11.Peek(16) == 0x3ee;
      assert s11.Peek(24) == 0xe7;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup7(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0b11);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s17, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 163
    * Starting at 0xb11
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xbb7

    requires s0.stack[8] == 0xbef

    requires s0.stack[16] == 0x3ee

    requires s0.stack[24] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbb7;
      assert s1.Peek(8) == 0xbef;
      assert s1.Peek(16) == 0x3ee;
      assert s1.Peek(24) == 0xe7;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s181(s2, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 164
    * Starting at 0xb14
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[4] == 0xbb7

    requires s0.stack[9] == 0xbef

    requires s0.stack[17] == 0x3ee

    requires s0.stack[25] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbb7;
      assert s1.Peek(9) == 0xbef;
      assert s1.Peek(17) == 0x3ee;
      assert s1.Peek(25) == 0xe7;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0b2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s7, gas - 1)
      else
        ExecuteFromCFGNode_s182(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 165
    * Starting at 0xb1d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[4] == 0xbb7

    requires s0.stack[9] == 0xbef

    requires s0.stack[17] == 0x3ee

    requires s0.stack[25] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0xbb7;
      assert s1.Peek(10) == 0xbef;
      assert s1.Peek(18) == 0x3ee;
      assert s1.Peek(26) == 0xe7;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0b14);
      assert s11.Peek(0) == 0xb14;
      assert s11.Peek(5) == 0xbb7;
      assert s11.Peek(10) == 0xbef;
      assert s11.Peek(18) == 0x3ee;
      assert s11.Peek(26) == 0xe7;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s12, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 166
    * Starting at 0xb2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[4] == 0xbb7

    requires s0.stack[9] == 0xbef

    requires s0.stack[17] == 0x3ee

    requires s0.stack[25] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbb7;
      assert s1.Peek(9) == 0xbef;
      assert s1.Peek(17) == 0x3ee;
      assert s1.Peek(25) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s8, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 171
    * Starting at 0xbb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xbef

    requires s0.stack[12] == 0x3ee

    requires s0.stack[20] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbef;
      assert s1.Peek(12) == 0x3ee;
      assert s1.Peek(20) == 0xe7;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(4) == 0xbef;
      assert s11.Peek(12) == 0x3ee;
      assert s11.Peek(20) == 0xe7;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s17, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 173
    * Starting at 0xbef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x3ee

    requires s0.stack[16] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3ee;
      assert s1.Peek(16) == 0xe7;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push2(s8, 0x0c01);
      var s10 := Dup2(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(2) == 0xc01;
      assert s11.Peek(11) == 0x3ee;
      assert s11.Peek(19) == 0xe7;
      var s12 := Push2(s11, 0x0b9f);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s13, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 170
    * Starting at 0xb9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xc01

    requires s0.stack[11] == 0x3ee

    requires s0.stack[19] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc01;
      assert s1.Peek(11) == 0x3ee;
      assert s1.Peek(19) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push2(s7, 0x0bb7);
      var s9 := Dup2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup7(s10);
      assert s11.Peek(3) == 0xbb7;
      assert s11.Peek(8) == 0xc01;
      assert s11.Peek(17) == 0x3ee;
      assert s11.Peek(25) == 0xe7;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup7(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0b11);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s17, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 163
    * Starting at 0xb11
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0xbb7

    requires s0.stack[8] == 0xc01

    requires s0.stack[17] == 0x3ee

    requires s0.stack[25] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbb7;
      assert s1.Peek(8) == 0xc01;
      assert s1.Peek(17) == 0x3ee;
      assert s1.Peek(25) == 0xe7;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s188(s2, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 164
    * Starting at 0xb14
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xbb7

    requires s0.stack[9] == 0xc01

    requires s0.stack[18] == 0x3ee

    requires s0.stack[26] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbb7;
      assert s1.Peek(9) == 0xc01;
      assert s1.Peek(18) == 0x3ee;
      assert s1.Peek(26) == 0xe7;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0b2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s190(s7, gas - 1)
      else
        ExecuteFromCFGNode_s189(s7, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 165
    * Starting at 0xb1d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xbb7

    requires s0.stack[9] == 0xc01

    requires s0.stack[18] == 0x3ee

    requires s0.stack[26] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0xbb7;
      assert s1.Peek(10) == 0xc01;
      assert s1.Peek(19) == 0x3ee;
      assert s1.Peek(27) == 0xe7;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0b14);
      assert s11.Peek(0) == 0xb14;
      assert s11.Peek(5) == 0xbb7;
      assert s11.Peek(10) == 0xc01;
      assert s11.Peek(19) == 0x3ee;
      assert s11.Peek(27) == 0xe7;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s12, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 166
    * Starting at 0xb2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xbb7

    requires s0.stack[9] == 0xc01

    requires s0.stack[18] == 0x3ee

    requires s0.stack[26] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbb7;
      assert s1.Peek(9) == 0xc01;
      assert s1.Peek(18) == 0x3ee;
      assert s1.Peek(26) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s8, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 171
    * Starting at 0xbb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0xc01

    requires s0.stack[13] == 0x3ee

    requires s0.stack[21] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc01;
      assert s1.Peek(13) == 0x3ee;
      assert s1.Peek(21) == 0xe7;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(4) == 0xc01;
      assert s11.Peek(13) == 0x3ee;
      assert s11.Peek(21) == 0xe7;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s17, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 174
    * Starting at 0xc01
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[9] == 0x3ee

    requires s0.stack[17] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x3ee;
      assert s1.Peek(17) == 0xe7;
      var s2 := Push1(s1, 0xff);
      var s3 := Swap6(s2);
      var s4 := Swap1(s3);
      var s5 := Swap6(s4);
      var s6 := And(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Pop(s10);
      assert s11.Peek(7) == 0x3ee;
      assert s11.Peek(15) == 0xe7;
      var s12 := Pop(s11);
      var s13 := Push1(s12, 0x80);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Swap4(s15);
      var s17 := Swap3(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s21, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 82
    * Starting at 0x3ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xe7;
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
      assert s11.Peek(15) == 0xe7;
      var s12 := ExtCodeSize(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0408);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s17, gas - 1)
      else
        ExecuteFromCFGNode_s194(s17, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 83
    * Starting at 0x404
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(16) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 195
    * Segment Id for this node is: 84
    * Starting at 0x408
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x408 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(15) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x041c);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s9, gas - 1)
      else
        ExecuteFromCFGNode_s196(s9, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 85
    * Starting at 0x413
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x413 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(10) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 197
    * Segment Id for this node is: 86
    * Starting at 0x41c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x042c);
      var s7 := Caller(s6);
      var s8 := Dup3(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Push2(s9, 0x0910);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s11, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 128
    * Starting at 0x910
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x910 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x42c

    requires s0.stack[9] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x42c;
      assert s1.Peek(9) == 0xe7;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x141106f5);
      var s5 := Push1(s4, 0xe1);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(7) == 0x42c;
      assert s11.Peek(13) == 0xe7;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := Dup5(s13);
      var s15 := Dup2(s14);
      var s16 := And(s15);
      var s17 := Push1(s16, 0x04);
      var s18 := Dup4(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(6) == 0x42c;
      assert s21.Peek(12) == 0xe7;
      var s22 := Dup2(s21);
      var s23 := And(s22);
      var s24 := Push1(s23, 0x24);
      var s25 := Dup4(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0xff);
      var s29 := Dup4(s28);
      var s30 := And(s29);
      var s31 := Push1(s30, 0x44);
      assert s31.Peek(7) == 0x42c;
      assert s31.Peek(13) == 0xe7;
      var s32 := Dup4(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push32(s34, 0x000000000000000000000000b2665bc2539b624f5905faede00802f77be73b2b);
      var s36 := And(s35);
      var s37 := Swap1(s36);
      var s38 := Push4(s37, 0x28220dea);
      var s39 := Swap1(s38);
      var s40 := Push1(s39, 0x64);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s199(s41, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 129
    * Starting at 0x96b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x42c

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x42c;
      assert s1.Peek(13) == 0xe7;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Dup8(s8);
      var s10 := Dup1(s9);
      var s11 := ExtCodeSize(s10);
      assert s11.Peek(13) == 0x42c;
      assert s11.Peek(19) == 0xe7;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0984);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s16, gas - 1)
      else
        ExecuteFromCFGNode_s200(s16, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 130
    * Starting at 0x980
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x980 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[13] == 0x42c

    requires s0.stack[19] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(14) == 0x42c;
      assert s1.Peek(20) == 0xe7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 201
    * Segment Id for this node is: 131
    * Starting at 0x984
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x984 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[13] == 0x42c

    requires s0.stack[19] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x42c;
      assert s1.Peek(19) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0998);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s9, gas - 1)
      else
        ExecuteFromCFGNode_s202(s9, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 132
    * Starting at 0x98f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x42c

    requires s0.stack[13] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(8) == 0x42c;
      assert s1.Peek(14) == 0xe7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 203
    * Segment Id for this node is: 133
    * Starting at 0x998
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x998 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x42c

    requires s0.stack[13] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x42c;
      assert s1.Peek(13) == 0xe7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s9, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 87
    * Starting at 0x42c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe7;
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup1(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x00);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(10) == 0xe7;
      var s12 := Shl(s11);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := Div(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x60);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := And(s20);
      assert s21.Peek(8) == 0xe7;
      var s22 := Push1(s21, 0x20);
      var s23 := Dup4(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0x01);
      var s28 := Push1(s27, 0xa0);
      var s29 := Shl(s28);
      var s30 := Sub(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0xe7;
      var s32 := And(s31);
      var s33 := Swap2(s32);
      var s34 := Caller(s33);
      var s35 := Swap2(s34);
      var s36 := Push32(s35, 0x2395b95c14d87a016c2bfcac5b35c32cd39f2127399d3ccc77e145d0a3099d41);
      var s37 := Swap2(s36);
      var s38 := Add(s37);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s205(s41, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 88
    * Starting at 0x482
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x482 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(11) == 0xe7;
      var s2 := Sub(s1);
      var s3 := Swap1(s2);
      var s4 := Log3(s3);
      var s5 := Push2(s4, 0x048e);
      var s6 := Push1(s5, 0x01);
      var s7 := Dup1(s6);
      var s8 := SStore(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s9, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 89
    * Starting at 0x48e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe7;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s8, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 121
    * Starting at 0x7ec
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x372

    requires s0.stack[12] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x372;
      assert s1.Peek(12) == 0xe7;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s156(s4, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 121
    * Starting at 0x7ec
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x5ba

    requires s0.stack[8] == 0x357

    requires s0.stack[14] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x5ba;
      assert s1.Peek(8) == 0x357;
      assert s1.Peek(14) == 0xe7;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s145(s4, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 12
    * Starting at 0x7f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x017e7e58);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00c7);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s6, gas - 1)
      else
        ExecuteFromCFGNode_s210(s6, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 13
    * Starting at 0x8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x06bfcec6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0104);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s5, gas - 1)
      else
        ExecuteFromCFGNode_s211(s5, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 14
    * Starting at 0x96
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23fa495a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0143);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s235(s5, gas - 1)
      else
        ExecuteFromCFGNode_s212(s5, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 15
    * Starting at 0xa1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x42246a57);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0165);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s232(s5, gas - 1)
      else
        ExecuteFromCFGNode_s213(s5, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 16
    * Starting at 0xac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x5c60da1b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0199);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s227(s5, gas - 1)
      else
        ExecuteFromCFGNode_s214(s5, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 17
    * Starting at 0xb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01b9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s216(s5, gas - 1)
      else
        ExecuteFromCFGNode_s215(s5, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 18
    * Starting at 0xc2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2 as nat
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

  /** Node 216
    * Segment Id for this node is: 39
    * Starting at 0x1b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b9 as nat
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
      var s5 := Push2(s4, 0x01c5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s6, gas - 1)
      else
        ExecuteFromCFGNode_s217(s6, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 40
    * Starting at 0x1c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
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

  /** Node 218
    * Segment Id for this node is: 41
    * Starting at 0x1c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0163);
      var s4 := Push2(s3, 0x030c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s5, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 71
    * Starting at 0x30c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x163;
      var s2 := Push2(s1, 0x0314);
      var s3 := Push2(s2, 0x062e);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s4, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 108
    * Starting at 0x62e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x314

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x314;
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x314;
      assert s11.Peek(2) == 0x163;
      var s12 := Push2(s11, 0x031e);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s223(s13, gas - 1)
      else
        ExecuteFromCFGNode_s221(s13, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 109
    * Starting at 0x641
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x641 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x314

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x314;
      assert s1.Peek(2) == 0x163;
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
      assert s11.Peek(3) == 0x314;
      assert s11.Peek(4) == 0x163;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x314;
      assert s21.Peek(5) == 0x163;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x02fe);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s27, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x314

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x314;
      assert s1.Peek(2) == 0x163;
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

  /** Node 223
    * Segment Id for this node is: 73
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x314

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x314;
      assert s1.Peek(1) == 0x163;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s2, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 72
    * Starting at 0x314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x163;
      var s2 := Push2(s1, 0x031e);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0688);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s5, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 110
    * Starting at 0x688
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x688 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x31e

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x31e;
      assert s1.Peek(2) == 0x163;
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
      assert s11.Peek(6) == 0x31e;
      assert s11.Peek(7) == 0x163;
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
      assert s21.Peek(7) == 0x31e;
      assert s21.Peek(8) == 0x163;
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
      assert s31.Peek(5) == 0x31e;
      assert s31.Peek(6) == 0x163;
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
      ExecuteFromCFGNode_s226(s40, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 73
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x163;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s2, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 36
    * Starting at 0x199
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x199 as nat
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
      var s5 := Push2(s4, 0x01a5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s229(s6, gas - 1)
      else
        ExecuteFromCFGNode_s228(s6, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 37
    * Starting at 0x1a1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a1 as nat
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

  /** Node 229
    * Segment Id for this node is: 38
    * Starting at 0x1a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x00e7);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0xe7;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s14, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 22
    * Starting at 0xe7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe7;
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
      assert s11.Peek(2) == 0xe7;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s231(s15, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 23
    * Starting at 0xfb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xe7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe7;
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

  /** Node 232
    * Segment Id for this node is: 33
    * Starting at 0x165
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x165 as nat
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
      var s5 := Push2(s4, 0x0171);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s234(s6, gas - 1)
      else
        ExecuteFromCFGNode_s233(s6, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 34
    * Starting at 0x16d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16d as nat
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

  /** Node 234
    * Segment Id for this node is: 35
    * Starting at 0x171
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00e7);
      var s4 := Push32(s3, 0x000000000000000000000000b2665bc2539b624f5905faede00802f77be73b2b);
      var s5 := Dup2(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s6, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 28
    * Starting at 0x143
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143 as nat
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
      var s5 := Push2(s4, 0x014f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s237(s6, gas - 1)
      else
        ExecuteFromCFGNode_s236(s6, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 29
    * Starting at 0x14b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b as nat
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

  /** Node 237
    * Segment Id for this node is: 30
    * Starting at 0x14f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0163);
      var s4 := Push2(s3, 0x015e);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x09a1);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s8, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 134
    * Starting at 0x9a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x15e

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15e;
      assert s1.Peek(3) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x09b3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s10, gas - 1)
      else
        ExecuteFromCFGNode_s239(s10, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 135
    * Starting at 0x9af
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x15e

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x15e;
      assert s1.Peek(5) == 0x163;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 240
    * Segment Id for this node is: 136
    * Starting at 0x9b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x15e

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x15e;
      assert s1.Peek(4) == 0x163;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s7, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 31
    * Starting at 0x15e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x02b7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s3, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 66
    * Starting at 0x2b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Push2(s2, 0x062e);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s4, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 108
    * Starting at 0x62e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x2bf

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2bf;
      assert s1.Peek(2) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x2bf;
      assert s11.Peek(3) == 0x163;
      var s12 := Push2(s11, 0x031e);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s246(s13, gas - 1)
      else
        ExecuteFromCFGNode_s244(s13, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 109
    * Starting at 0x641
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x641 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x2bf

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x2bf;
      assert s1.Peek(3) == 0x163;
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
      assert s11.Peek(3) == 0x2bf;
      assert s11.Peek(5) == 0x163;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x2bf;
      assert s21.Peek(6) == 0x163;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x02fe);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s27, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 69
    * Starting at 0x2fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x2bf

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2bf;
      assert s1.Peek(3) == 0x163;
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

  /** Node 246
    * Segment Id for this node is: 73
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x2bf

    requires s0.stack[2] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2bf;
      assert s1.Peek(2) == 0x163;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s2, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 67
    * Starting at 0x2bf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push32(s1, 0x00000000000000000000000000000000000000000052b7d2dcc80cd2e4000000);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0307);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s249(s6, gas - 1)
      else
        ExecuteFromCFGNode_s248(s6, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 68
    * Starting at 0x2e7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x163;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x179c6377);
      var s4 := Push1(s3, 0xe1);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(4) == 0x163;
      var s12 := Swap1(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x24);
      var s15 := Add(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s26(s15, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 70
    * Starting at 0x307
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x307 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x04);
      var s3 := SStore(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s4, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 24
    * Starting at 0x104
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104 as nat
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
      var s5 := Push2(s4, 0x0110);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s6, gas - 1)
      else
        ExecuteFromCFGNode_s251(s6, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 25
    * Starting at 0x10c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c as nat
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

  /** Node 252
    * Segment Id for this node is: 26
    * Starting at 0x110
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x012b);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(1) == 0x12b;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x60);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := And(s16);
      var s18 := Dup2(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s19, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 27
    * Starting at 0x12b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x60);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Swap1(s8);
      var s10 := Swap2(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x12b;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x00fb);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s17, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 23
    * Starting at 0xfb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12b;
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

  /** Node 255
    * Segment Id for this node is: 19
    * Starting at 0xc7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7 as nat
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
      var s5 := Push2(s4, 0x00d3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s257(s6, gas - 1)
      else
        ExecuteFromCFGNode_s256(s6, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 20
    * Starting at 0xcf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
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

  /** Node 257
    * Segment Id for this node is: 21
    * Starting at 0xd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x00e7);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0xe7;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s14, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 18
    * Starting at 0xc2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2 as nat
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
