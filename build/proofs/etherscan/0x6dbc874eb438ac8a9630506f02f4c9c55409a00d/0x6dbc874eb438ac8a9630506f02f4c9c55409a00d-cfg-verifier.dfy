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
      var s6 := Push2(s5, 0x00cd);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s691(s7, gas - 1)
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
      var s6 := Push4(s5, 0x70a08231);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x008a);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s327(s9, gas - 1)
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
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0064);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s264(s5, gas - 1)
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
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ff);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x021d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x4a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x024d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x55
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x027d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00cd);
      assert s1.Peek(0) == 0xcd;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 20
    * Starting at 0xcd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd as nat
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

  /** Node 11
    * Segment Id for this node is: 61
    * Starting at 0x27d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0297);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0292);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x292;
      assert s11.Peek(3) == 0x297;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x107c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s14, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 216
    * Starting at 0x107c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x292

    requires s0.stack[3] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(3) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1091);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s10, gas - 1)
      else
        ExecuteFromCFGNode_s13(s10, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 217
    * Starting at 0x1089
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1089 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x292

    requires s0.stack[4] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1090);
      assert s1.Peek(0) == 0x1090;
      assert s1.Peek(4) == 0x292;
      assert s1.Peek(5) == 0x297;
      var s2 := Push2(s1, 0x0f52);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s3, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 184
    * Starting at 0xf52
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x1090

    requires s0.stack[4] == 0x292

    requires s0.stack[5] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1090;
      assert s1.Peek(4) == 0x292;
      assert s1.Peek(5) == 0x297;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 15
    * Segment Id for this node is: 219
    * Starting at 0x1091
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1091 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x292

    requires s0.stack[4] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x292;
      assert s1.Peek(4) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x109e);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0f9c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s9, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x109e

    requires s0.stack[7] == 0x292

    requires s0.stack[8] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109e;
      assert s1.Peek(7) == 0x292;
      assert s1.Peek(8) == 0x297;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s10, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x292

    requires s0.stack[11] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x109e;
      assert s1.Peek(10) == 0x292;
      assert s1.Peek(11) == 0x297;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s5, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x109e

    requires s0.stack[12] == 0x292

    requires s0.stack[13] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x109e;
      assert s1.Peek(12) == 0x292;
      assert s1.Peek(13) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s6, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x109e

    requires s0.stack[15] == 0x292

    requires s0.stack[16] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x109e;
      assert s1.Peek(15) == 0x292;
      assert s1.Peek(16) == 0x297;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s20(s11, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x109e

    requires s0.stack[14] == 0x292

    requires s0.stack[15] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x109e;
      assert s1.Peek(14) == 0x292;
      assert s1.Peek(15) == 0x297;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s7, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x109e

    requires s0.stack[11] == 0x292

    requires s0.stack[12] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x109e;
      assert s1.Peek(11) == 0x292;
      assert s1.Peek(12) == 0x297;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s5, gas - 1)
      else
        ExecuteFromCFGNode_s22(s5, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x292

    requires s0.stack[11] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x109e;
      assert s1.Peek(11) == 0x292;
      assert s1.Peek(12) == 0x297;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 23
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x292

    requires s0.stack[11] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x109e;
      assert s1.Peek(10) == 0x292;
      assert s1.Peek(11) == 0x297;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s3, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x109e

    requires s0.stack[8] == 0x292

    requires s0.stack[9] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x109e;
      assert s1.Peek(8) == 0x292;
      assert s1.Peek(9) == 0x297;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s6, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 220
    * Starting at 0x109e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x292

    requires s0.stack[6] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x292;
      assert s1.Peek(6) == 0x297;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s9, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 62
    * Starting at 0x292
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x297;
      var s2 := Push2(s1, 0x0620);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s3, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 105
    * Starting at 0x620
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x620 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x297;
      var s2 := Push2(s1, 0x0628);
      var s3 := Push2(s2, 0x06bd);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s4, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 114
    * Starting at 0x6bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x628

    requires s0.stack[2] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x628;
      assert s1.Peek(2) == 0x297;
      var s2 := Push2(s1, 0x06c5);
      var s3 := Push2(s2, 0x06a4);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s4, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x6c5

    requires s0.stack[1] == 0x628

    requires s0.stack[3] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6c5;
      assert s1.Peek(1) == 0x628;
      assert s1.Peek(3) == 0x297;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s7, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 115
    * Starting at 0x6c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x628

    requires s0.stack[3] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x628;
      assert s1.Peek(3) == 0x297;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x06e3);
      var s5 := Push2(s4, 0x04c4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s6, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 90
    * Starting at 0x4c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x6e3

    requires s0.stack[2] == 0x628

    requires s0.stack[4] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6e3;
      assert s1.Peek(2) == 0x628;
      assert s1.Peek(4) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x07);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x6e3;
      assert s11.Peek(4) == 0x628;
      assert s11.Peek(6) == 0x297;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s17, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 116
    * Starting at 0x6e3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x628

    requires s0.stack[4] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x628;
      assert s1.Peek(4) == 0x297;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0742);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s6, gas - 1)
      else
        ExecuteFromCFGNode_s33(s6, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 117
    * Starting at 0x6ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x628

    requires s0.stack[2] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0706);
      assert s1.Peek(0) == 0x706;
      assert s1.Peek(1) == 0x628;
      assert s1.Peek(3) == 0x297;
      var s2 := Push2(s1, 0x06a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s3, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x706

    requires s0.stack[1] == 0x628

    requires s0.stack[3] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x706;
      assert s1.Peek(1) == 0x628;
      assert s1.Peek(3) == 0x297;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s7, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 118
    * Starting at 0x706
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x706 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x628

    requires s0.stack[3] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x628;
      assert s1.Peek(3) == 0x297;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0739);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x739;
      assert s11.Peek(3) == 0x628;
      assert s11.Peek(5) == 0x297;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s13, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x739

    requires s0.stack[3] == 0x628

    requires s0.stack[5] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x739;
      assert s1.Peek(3) == 0x628;
      assert s1.Peek(5) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x739;
      assert s11.Peek(6) == 0x628;
      assert s11.Peek(8) == 0x297;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s14, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x739

    requires s0.stack[7] == 0x628

    requires s0.stack[9] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x739;
      assert s1.Peek(7) == 0x628;
      assert s1.Peek(9) == 0x297;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s5, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x739

    requires s0.stack[9] == 0x628

    requires s0.stack[11] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x739;
      assert s1.Peek(9) == 0x628;
      assert s1.Peek(11) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s6, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x739

    requires s0.stack[12] == 0x628

    requires s0.stack[14] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x739;
      assert s1.Peek(12) == 0x628;
      assert s1.Peek(14) == 0x297;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s40(s11, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x739

    requires s0.stack[11] == 0x628

    requires s0.stack[13] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x739;
      assert s1.Peek(11) == 0x628;
      assert s1.Peek(13) == 0x297;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s7, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x739

    requires s0.stack[8] == 0x628

    requires s0.stack[10] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x739;
      assert s1.Peek(8) == 0x628;
      assert s1.Peek(10) == 0x297;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s6, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x739

    requires s0.stack[4] == 0x628

    requires s0.stack[6] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x739;
      assert s1.Peek(4) == 0x628;
      assert s1.Peek(6) == 0x297;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s6, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 119
    * Starting at 0x739
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x628

    requires s0.stack[3] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x628;
      assert s1.Peek(3) == 0x297;
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

  /** Node 44
    * Segment Id for this node is: 120
    * Starting at 0x742
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x742 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x628

    requires s0.stack[2] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x628;
      assert s1.Peek(2) == 0x297;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s2, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 106
    * Starting at 0x628
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x628 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0698);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s10, gas - 1)
      else
        ExecuteFromCFGNode_s46(s10, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 107
    * Starting at 0x65c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x297;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x1e4fbdf700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x068f);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x68f;
      assert s11.Peek(4) == 0x297;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s13, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x68f

    requires s0.stack[4] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x68f;
      assert s1.Peek(4) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x68f;
      assert s11.Peek(7) == 0x297;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s14, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x68f

    requires s0.stack[8] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x68f;
      assert s1.Peek(8) == 0x297;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s5, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x68f

    requires s0.stack[10] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x68f;
      assert s1.Peek(10) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s6, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x68f

    requires s0.stack[13] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x68f;
      assert s1.Peek(13) == 0x297;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s51(s11, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x68f

    requires s0.stack[12] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x68f;
      assert s1.Peek(12) == 0x297;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s7, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x68f

    requires s0.stack[9] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x68f;
      assert s1.Peek(9) == 0x297;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s6, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x68f

    requires s0.stack[5] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x68f;
      assert s1.Peek(5) == 0x297;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 108
    * Starting at 0x68f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x297;
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
    * Segment Id for this node is: 109
    * Starting at 0x698
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x698 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x297;
      var s2 := Push2(s1, 0x06a1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08c6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s5, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 137
    * Starting at 0x8c6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x6a1

    requires s0.stack[3] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6a1;
      assert s1.Peek(3) == 0x297;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x07);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x6a1;
      assert s11.Peek(5) == 0x297;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x07);
      var s18 := Push0(s17);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x6a1;
      assert s21.Peek(8) == 0x297;
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
      assert s31.Peek(7) == 0x6a1;
      assert s31.Peek(9) == 0x297;
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
      ExecuteFromCFGNode_s57(s41, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 138
    * Starting at 0x959
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x959 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x6a1

    requires s0.stack[7] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x6a1;
      assert s1.Peek(6) == 0x297;
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
      assert s11.Peek(2) == 0x6a1;
      assert s11.Peek(4) == 0x297;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s14, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 110
    * Starting at 0x6a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x297

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x297;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s3, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 63
    * Starting at 0x297
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x297 as nat
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

  /** Node 60
    * Segment Id for this node is: 57
    * Starting at 0x24d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0267);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0262);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x262;
      assert s11.Peek(3) == 0x267;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x1153);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s14, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 237
    * Starting at 0x1153
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1153 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x262

    requires s0.stack[3] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x262;
      assert s1.Peek(3) == 0x267;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x1169);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s11, gas - 1)
      else
        ExecuteFromCFGNode_s62(s11, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 238
    * Starting at 0x1161
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1161 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x262

    requires s0.stack[5] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1168);
      assert s1.Peek(0) == 0x1168;
      assert s1.Peek(5) == 0x262;
      assert s1.Peek(6) == 0x267;
      var s2 := Push2(s1, 0x0f52);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s3, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 184
    * Starting at 0xf52
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x1168

    requires s0.stack[5] == 0x262

    requires s0.stack[6] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1168;
      assert s1.Peek(5) == 0x262;
      assert s1.Peek(6) == 0x267;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 64
    * Segment Id for this node is: 240
    * Starting at 0x1169
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1169 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x262

    requires s0.stack[5] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x262;
      assert s1.Peek(5) == 0x267;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1176);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0f9c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s9, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1176

    requires s0.stack[8] == 0x262

    requires s0.stack[9] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1176;
      assert s1.Peek(8) == 0x262;
      assert s1.Peek(9) == 0x267;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s10, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1176

    requires s0.stack[11] == 0x262

    requires s0.stack[12] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x1176;
      assert s1.Peek(11) == 0x262;
      assert s1.Peek(12) == 0x267;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s5, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x1176

    requires s0.stack[13] == 0x262

    requires s0.stack[14] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x1176;
      assert s1.Peek(13) == 0x262;
      assert s1.Peek(14) == 0x267;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s6, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x1176

    requires s0.stack[16] == 0x262

    requires s0.stack[17] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x1176;
      assert s1.Peek(16) == 0x262;
      assert s1.Peek(17) == 0x267;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s69(s11, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x1176

    requires s0.stack[15] == 0x262

    requires s0.stack[16] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x1176;
      assert s1.Peek(15) == 0x262;
      assert s1.Peek(16) == 0x267;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s7, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x1176

    requires s0.stack[12] == 0x262

    requires s0.stack[13] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x1176;
      assert s1.Peek(12) == 0x262;
      assert s1.Peek(13) == 0x267;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s5, gas - 1)
      else
        ExecuteFromCFGNode_s71(s5, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1176

    requires s0.stack[11] == 0x262

    requires s0.stack[12] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x1176;
      assert s1.Peek(12) == 0x262;
      assert s1.Peek(13) == 0x267;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 72
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1176

    requires s0.stack[11] == 0x262

    requires s0.stack[12] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x1176;
      assert s1.Peek(11) == 0x262;
      assert s1.Peek(12) == 0x267;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1176

    requires s0.stack[9] == 0x262

    requires s0.stack[10] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1176;
      assert s1.Peek(9) == 0x262;
      assert s1.Peek(10) == 0x267;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s6, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 241
    * Starting at 0x1176
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1176 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x262

    requires s0.stack[7] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x262;
      assert s1.Peek(7) == 0x267;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x1187);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0f9c);
      assert s11.Peek(0) == 0xf9c;
      assert s11.Peek(3) == 0x1187;
      assert s11.Peek(9) == 0x262;
      assert s11.Peek(10) == 0x267;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s12, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1187

    requires s0.stack[8] == 0x262

    requires s0.stack[9] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1187;
      assert s1.Peek(8) == 0x262;
      assert s1.Peek(9) == 0x267;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s10, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1187

    requires s0.stack[11] == 0x262

    requires s0.stack[12] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x1187;
      assert s1.Peek(11) == 0x262;
      assert s1.Peek(12) == 0x267;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s5, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x1187

    requires s0.stack[13] == 0x262

    requires s0.stack[14] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x1187;
      assert s1.Peek(13) == 0x262;
      assert s1.Peek(14) == 0x267;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s6, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x1187

    requires s0.stack[16] == 0x262

    requires s0.stack[17] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x1187;
      assert s1.Peek(16) == 0x262;
      assert s1.Peek(17) == 0x267;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s79(s11, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x1187

    requires s0.stack[15] == 0x262

    requires s0.stack[16] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x1187;
      assert s1.Peek(15) == 0x262;
      assert s1.Peek(16) == 0x267;
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
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x1187

    requires s0.stack[12] == 0x262

    requires s0.stack[13] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x1187;
      assert s1.Peek(12) == 0x262;
      assert s1.Peek(13) == 0x267;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s5, gas - 1)
      else
        ExecuteFromCFGNode_s81(s5, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1187

    requires s0.stack[11] == 0x262

    requires s0.stack[12] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x1187;
      assert s1.Peek(12) == 0x262;
      assert s1.Peek(13) == 0x267;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 82
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1187

    requires s0.stack[11] == 0x262

    requires s0.stack[12] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x1187;
      assert s1.Peek(11) == 0x262;
      assert s1.Peek(12) == 0x267;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s3, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1187

    requires s0.stack[9] == 0x262

    requires s0.stack[10] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1187;
      assert s1.Peek(9) == 0x262;
      assert s1.Peek(10) == 0x267;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s6, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 242
    * Starting at 0x1187
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1187 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x262

    requires s0.stack[7] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x262;
      assert s1.Peek(7) == 0x267;
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
      ExecuteFromCFGNode_s85(s10, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 58
    * Starting at 0x262
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x262 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x267;
      var s2 := Push2(s1, 0x059e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s3, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 103
    * Starting at 0x59e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x267;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x267;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(5) == 0x267;
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
      assert s31.Peek(5) == 0x267;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s87(s41, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 104
    * Starting at 0x61c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x267

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x267;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s4, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 59
    * Starting at 0x267
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x267 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0274);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1063);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s8, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 214
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x274

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x274;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1076);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1076;
      assert s11.Peek(5) == 0x274;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x1054);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s14, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1076

    requires s0.stack[6] == 0x274

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1076;
      assert s1.Peek(6) == 0x274;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s5, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x1076

    requires s0.stack[8] == 0x274

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x1076;
      assert s1.Peek(8) == 0x274;
      var s2 := Push0(s1);
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
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1076

    requires s0.stack[7] == 0x274

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1076;
      assert s1.Peek(7) == 0x274;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s6, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 215
    * Starting at 0x1076
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1076 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x274

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x274;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s6, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 60
    * Starting at 0x274
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x274 as nat
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

  /** Node 95
    * Segment Id for this node is: 53
    * Starting at 0x21d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0237);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0232);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x232;
      assert s11.Peek(3) == 0x237;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0fe3);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s14, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 201
    * Starting at 0xfe3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x232

    requires s0.stack[3] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x232;
      assert s1.Peek(3) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0ff9);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s11, gas - 1)
      else
        ExecuteFromCFGNode_s97(s11, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 202
    * Starting at 0xff1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x232

    requires s0.stack[5] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ff8);
      assert s1.Peek(0) == 0xff8;
      assert s1.Peek(5) == 0x232;
      assert s1.Peek(6) == 0x237;
      var s2 := Push2(s1, 0x0f52);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s3, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 184
    * Starting at 0xf52
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xff8

    requires s0.stack[5] == 0x232

    requires s0.stack[6] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xff8;
      assert s1.Peek(5) == 0x232;
      assert s1.Peek(6) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 99
    * Segment Id for this node is: 204
    * Starting at 0xff9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x232

    requires s0.stack[5] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x232;
      assert s1.Peek(5) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1006);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0f9c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s9, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1006

    requires s0.stack[8] == 0x232

    requires s0.stack[9] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1006;
      assert s1.Peek(8) == 0x232;
      assert s1.Peek(9) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s10, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1006

    requires s0.stack[11] == 0x232

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x1006;
      assert s1.Peek(11) == 0x232;
      assert s1.Peek(12) == 0x237;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s5, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x1006

    requires s0.stack[13] == 0x232

    requires s0.stack[14] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x1006;
      assert s1.Peek(13) == 0x232;
      assert s1.Peek(14) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s6, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x1006

    requires s0.stack[16] == 0x232

    requires s0.stack[17] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x1006;
      assert s1.Peek(16) == 0x232;
      assert s1.Peek(17) == 0x237;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s104(s11, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x1006

    requires s0.stack[15] == 0x232

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x1006;
      assert s1.Peek(15) == 0x232;
      assert s1.Peek(16) == 0x237;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s7, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x1006

    requires s0.stack[12] == 0x232

    requires s0.stack[13] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x1006;
      assert s1.Peek(12) == 0x232;
      assert s1.Peek(13) == 0x237;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s5, gas - 1)
      else
        ExecuteFromCFGNode_s106(s5, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1006

    requires s0.stack[11] == 0x232

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x1006;
      assert s1.Peek(12) == 0x232;
      assert s1.Peek(13) == 0x237;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 107
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1006

    requires s0.stack[11] == 0x232

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x1006;
      assert s1.Peek(11) == 0x232;
      assert s1.Peek(12) == 0x237;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s3, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1006

    requires s0.stack[9] == 0x232

    requires s0.stack[10] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1006;
      assert s1.Peek(9) == 0x232;
      assert s1.Peek(10) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s6, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 205
    * Starting at 0x1006
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1006 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x232

    requires s0.stack[7] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x232;
      assert s1.Peek(7) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x1017);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0fcf);
      assert s11.Peek(0) == 0xfcf;
      assert s11.Peek(3) == 0x1017;
      assert s11.Peek(9) == 0x232;
      assert s11.Peek(10) == 0x237;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s12, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 199
    * Starting at 0xfcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1017

    requires s0.stack[8] == 0x232

    requires s0.stack[9] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1017;
      assert s1.Peek(8) == 0x232;
      assert s1.Peek(9) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0fdd);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fb9);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s10, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 195
    * Starting at 0xfb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x1017

    requires s0.stack[11] == 0x232

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfdd;
      assert s1.Peek(5) == 0x1017;
      assert s1.Peek(11) == 0x232;
      assert s1.Peek(12) == 0x237;
      var s2 := Push2(s1, 0x0fc2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s5, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xfc2

    requires s0.stack[3] == 0xfdd

    requires s0.stack[7] == 0x1017

    requires s0.stack[13] == 0x232

    requires s0.stack[14] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfc2;
      assert s1.Peek(3) == 0xfdd;
      assert s1.Peek(7) == 0x1017;
      assert s1.Peek(13) == 0x232;
      assert s1.Peek(14) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s9, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 196
    * Starting at 0xfc2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xfdd

    requires s0.stack[6] == 0x1017

    requires s0.stack[12] == 0x232

    requires s0.stack[13] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfdd;
      assert s1.Peek(6) == 0x1017;
      assert s1.Peek(12) == 0x232;
      assert s1.Peek(13) == 0x237;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0fcc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s115(s5, gas - 1)
      else
        ExecuteFromCFGNode_s114(s5, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 197
    * Starting at 0xfc9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x1017

    requires s0.stack[11] == 0x232

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfdd;
      assert s1.Peek(6) == 0x1017;
      assert s1.Peek(12) == 0x232;
      assert s1.Peek(13) == 0x237;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 115
    * Segment Id for this node is: 198
    * Starting at 0xfcc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x1017

    requires s0.stack[11] == 0x232

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfdd;
      assert s1.Peek(5) == 0x1017;
      assert s1.Peek(11) == 0x232;
      assert s1.Peek(12) == 0x237;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s3, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 200
    * Starting at 0xfdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1017

    requires s0.stack[9] == 0x232

    requires s0.stack[10] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1017;
      assert s1.Peek(9) == 0x232;
      assert s1.Peek(10) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s6, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 206
    * Starting at 0x1017
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1017 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x232

    requires s0.stack[7] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x232;
      assert s1.Peek(7) == 0x237;
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
      ExecuteFromCFGNode_s118(s10, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 54
    * Starting at 0x232
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x232 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x237;
      var s2 := Push2(s1, 0x057c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s3, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 100
    * Starting at 0x57c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0586);
      var s5 := Push2(s4, 0x06a4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s6, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x586

    requires s0.stack[5] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x586;
      assert s1.Peek(5) == 0x237;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s7, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 101
    * Starting at 0x586
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x586 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x237;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0593);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x07d6);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s9, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 129
    * Starting at 0x7d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x593

    requires s0.stack[8] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x593;
      assert s1.Peek(8) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0846);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s10, gas - 1)
      else
        ExecuteFromCFGNode_s123(s10, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 130
    * Starting at 0x80a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x593

    requires s0.stack[8] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x593;
      assert s1.Peek(9) == 0x237;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x96c6fd1e00000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x083d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x83d;
      assert s11.Peek(6) == 0x593;
      assert s11.Peek(11) == 0x237;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s13, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x83d

    requires s0.stack[6] == 0x593

    requires s0.stack[11] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x83d;
      assert s1.Peek(6) == 0x593;
      assert s1.Peek(11) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x83d;
      assert s11.Peek(9) == 0x593;
      assert s11.Peek(14) == 0x237;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s14, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x83d

    requires s0.stack[10] == 0x593

    requires s0.stack[15] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x83d;
      assert s1.Peek(10) == 0x593;
      assert s1.Peek(15) == 0x237;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s5, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x83d

    requires s0.stack[12] == 0x593

    requires s0.stack[17] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x83d;
      assert s1.Peek(12) == 0x593;
      assert s1.Peek(17) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s6, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x83d

    requires s0.stack[15] == 0x593

    requires s0.stack[20] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x83d;
      assert s1.Peek(15) == 0x593;
      assert s1.Peek(20) == 0x237;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s128(s11, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x83d

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x83d;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s7, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x83d

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x83d;
      assert s1.Peek(11) == 0x593;
      assert s1.Peek(16) == 0x237;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s6, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x83d

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x83d;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s6, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 131
    * Starting at 0x83d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x593

    requires s0.stack[9] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x593;
      assert s1.Peek(9) == 0x237;
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

  /** Node 132
    * Segment Id for this node is: 132
    * Starting at 0x846
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x846 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x593

    requires s0.stack[8] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x593;
      assert s1.Peek(8) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x08b6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s142(s10, gas - 1)
      else
        ExecuteFromCFGNode_s133(s10, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 133
    * Starting at 0x87a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x593

    requires s0.stack[8] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x593;
      assert s1.Peek(9) == 0x237;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xec442f0500000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x08ad);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x8ad;
      assert s11.Peek(6) == 0x593;
      assert s11.Peek(11) == 0x237;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s13, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x8ad

    requires s0.stack[6] == 0x593

    requires s0.stack[11] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8ad;
      assert s1.Peek(6) == 0x593;
      assert s1.Peek(11) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x8ad;
      assert s11.Peek(9) == 0x593;
      assert s11.Peek(14) == 0x237;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s14, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x8ad

    requires s0.stack[10] == 0x593

    requires s0.stack[15] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x8ad;
      assert s1.Peek(10) == 0x593;
      assert s1.Peek(15) == 0x237;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s5, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x8ad

    requires s0.stack[12] == 0x593

    requires s0.stack[17] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x8ad;
      assert s1.Peek(12) == 0x593;
      assert s1.Peek(17) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s6, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x8ad

    requires s0.stack[15] == 0x593

    requires s0.stack[20] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x8ad;
      assert s1.Peek(15) == 0x593;
      assert s1.Peek(20) == 0x237;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s138(s11, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x8ad

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x8ad;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s7, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x8ad

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x8ad;
      assert s1.Peek(11) == 0x593;
      assert s1.Peek(16) == 0x237;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s6, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8ad

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ad;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s6, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 134
    * Starting at 0x8ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x593

    requires s0.stack[9] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x593;
      assert s1.Peek(9) == 0x237;
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

  /** Node 142
    * Segment Id for this node is: 135
    * Starting at 0x8b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x593

    requires s0.stack[8] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x593;
      assert s1.Peek(8) == 0x237;
      var s2 := Push2(s1, 0x08c1);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b58);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s7, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 150
    * Starting at 0xb58
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0ba8);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s10, gas - 1)
      else
        ExecuteFromCFGNode_s144(s10, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 151
    * Starting at 0xb8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x593;
      assert s1.Peek(13) == 0x237;
      var s2 := Push1(s1, 0x03);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := SLoad(s5);
      var s7 := Push2(s6, 0x0b9c);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1250);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s11, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 255
    * Starting at 0x1250
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1250 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xb9c

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb9c;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x125a);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0fb0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s6, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x125a

    requires s0.stack[5] == 0xb9c

    requires s0.stack[12] == 0x8c1

    requires s0.stack[16] == 0x593

    requires s0.stack[21] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x125a;
      assert s1.Peek(5) == 0xb9c;
      assert s1.Peek(12) == 0x8c1;
      assert s1.Peek(16) == 0x593;
      assert s1.Peek(21) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s9, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 256
    * Starting at 0x125a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xb9c

    requires s0.stack[11] == 0x8c1

    requires s0.stack[15] == 0x593

    requires s0.stack[20] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb9c;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x593;
      assert s1.Peek(20) == 0x237;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1265);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0fb0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s7, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x1265

    requires s0.stack[5] == 0xb9c

    requires s0.stack[12] == 0x8c1

    requires s0.stack[16] == 0x593

    requires s0.stack[21] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1265;
      assert s1.Peek(5) == 0xb9c;
      assert s1.Peek(12) == 0x8c1;
      assert s1.Peek(16) == 0x593;
      assert s1.Peek(21) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s9, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 257
    * Starting at 0x1265
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xb9c

    requires s0.stack[11] == 0x8c1

    requires s0.stack[15] == 0x593

    requires s0.stack[20] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb9c;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x593;
      assert s1.Peek(20) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xb9c;
      assert s11.Peek(11) == 0x8c1;
      assert s11.Peek(15) == 0x593;
      assert s11.Peek(20) == 0x237;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x127d);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s14, gas - 1)
      else
        ExecuteFromCFGNode_s150(s14, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 258
    * Starting at 0x1275
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1275 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xb9c

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x127c);
      assert s1.Peek(0) == 0x127c;
      assert s1.Peek(4) == 0xb9c;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x593;
      assert s1.Peek(20) == 0x237;
      var s2 := Push2(s1, 0x1223);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s3, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 254
    * Starting at 0x1223
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1223 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x127c

    requires s0.stack[4] == 0xb9c

    requires s0.stack[11] == 0x8c1

    requires s0.stack[15] == 0x593

    requires s0.stack[20] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x127c;
      assert s1.Peek(4) == 0xb9c;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x593;
      assert s1.Peek(20) == 0x237;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 152
    * Segment Id for this node is: 260
    * Starting at 0x127d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xb9c

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb9c;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s6, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 152
    * Starting at 0xb9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x593;
      assert s1.Peek(16) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Push2(s8, 0x0c76);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s10, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 157
    * Starting at 0xc76
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0cbd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s10, gas - 1)
      else
        ExecuteFromCFGNode_s155(s10, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 158
    * Starting at 0xcaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x593;
      assert s1.Peek(13) == 0x237;
      var s2 := Push1(s1, 0x03);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := SLoad(s5);
      var s7 := Sub(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x593;
      assert s11.Peek(15) == 0x237;
      var s12 := Swap1(s11);
      var s13 := SStore(s12);
      var s14 := Pop(s13);
      var s15 := Push2(s14, 0x0db4);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s16, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 166
    * Starting at 0xdb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Push1(s1, 0xe4);
      var s3 := Push1(s2, 0x02);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x593;
      assert s11.Peek(15) == 0x237;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x8c1;
      assert s21.Peek(9) == 0x593;
      assert s21.Peek(14) == 0x237;
      var s22 := Sub(s21);
      var s23 := Push2(s22, 0x0e3e);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s24, gas - 1)
      else
        ExecuteFromCFGNode_s157(s24, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 167
    * Starting at 0xdfa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f20);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x593;
      assert s1.Peek(13) == 0x237;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Dup5(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(7) == 0x8c1;
      assert s11.Peek(11) == 0x593;
      assert s11.Peek(16) == 0x237;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(6) == 0x8c1;
      assert s21.Peek(10) == 0x593;
      assert s21.Peek(15) == 0x237;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s158(s23, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 168
    * Starting at 0xe3e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Dup2(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push32(s7, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x8c1;
      assert s11.Peek(12) == 0x593;
      assert s11.Peek(17) == 0x237;
      var s12 := Push2(s11, 0x0e9b);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x1063);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s16, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 214
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xe9b

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe9b;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1076);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1076;
      assert s11.Peek(5) == 0xe9b;
      assert s11.Peek(12) == 0x8c1;
      assert s11.Peek(16) == 0x593;
      assert s11.Peek(21) == 0x237;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x1054);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s14, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x1076

    requires s0.stack[6] == 0xe9b

    requires s0.stack[13] == 0x8c1

    requires s0.stack[17] == 0x593

    requires s0.stack[22] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1076;
      assert s1.Peek(6) == 0xe9b;
      assert s1.Peek(13) == 0x8c1;
      assert s1.Peek(17) == 0x593;
      assert s1.Peek(22) == 0x237;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s5, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x1076

    requires s0.stack[8] == 0xe9b

    requires s0.stack[15] == 0x8c1

    requires s0.stack[19] == 0x593

    requires s0.stack[24] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x1076;
      assert s1.Peek(8) == 0xe9b;
      assert s1.Peek(15) == 0x8c1;
      assert s1.Peek(19) == 0x593;
      assert s1.Peek(24) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s9, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x1076

    requires s0.stack[7] == 0xe9b

    requires s0.stack[14] == 0x8c1

    requires s0.stack[18] == 0x593

    requires s0.stack[23] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1076;
      assert s1.Peek(7) == 0xe9b;
      assert s1.Peek(14) == 0x8c1;
      assert s1.Peek(18) == 0x593;
      assert s1.Peek(23) == 0x237;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s6, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 215
    * Starting at 0x1076
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1076 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xe9b

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe9b;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s6, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 169
    * Starting at 0xe9b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x593;
      assert s1.Peek(16) == 0x237;
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
      assert s11.Peek(0) == 0x8c1;
      assert s11.Peek(4) == 0x593;
      assert s11.Peek(9) == 0x237;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s12, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 136
    * Starting at 0x8c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x593

    requires s0.stack[8] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x593;
      assert s1.Peek(8) == 0x237;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s5, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 102
    * Starting at 0x593
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x237;
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
      ExecuteFromCFGNode_s167(s10, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 55
    * Starting at 0x237
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x237 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0244);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x103b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s8, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 210
    * Starting at 0x103b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x244

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x244;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x104e);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x104e;
      assert s11.Peek(5) == 0x244;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x102c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s14, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 208
    * Starting at 0x102c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x104e

    requires s0.stack[6] == 0x244

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x104e;
      assert s1.Peek(6) == 0x244;
      var s2 := Push2(s1, 0x1035);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1021);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s5, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 207
    * Starting at 0x1021
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1021 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1035

    requires s0.stack[4] == 0x104e

    requires s0.stack[8] == 0x244

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1035;
      assert s1.Peek(4) == 0x104e;
      assert s1.Peek(8) == 0x244;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s171(s11, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 209
    * Starting at 0x1035
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x104e

    requires s0.stack[7] == 0x244

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x104e;
      assert s1.Peek(7) == 0x244;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s6, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 211
    * Starting at 0x104e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x244

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x244;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s6, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 56
    * Starting at 0x244
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x244 as nat
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

  /** Node 174
    * Segment Id for this node is: 159
    * Starting at 0xcbd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Push2(s1, 0x0f20);
      var s3 := Push1(s2, 0x02);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x593;
      assert s11.Peek(15) == 0x237;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x8c1;
      assert s21.Peek(9) == 0x593;
      assert s21.Peek(14) == 0x237;
      var s22 := Push1(s21, 0x02);
      var s23 := Push0(s22);
      var s24 := Dup7(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Push20(s26, 0xffffffffffffffffffffffffffffffffffffffff);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(8) == 0x8c1;
      assert s31.Peek(12) == 0x593;
      assert s31.Peek(17) == 0x237;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Dup2(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x20);
      var s37 := Add(s36);
      var s38 := Push0(s37);
      var s39 := Keccak256(s38);
      var s40 := SLoad(s39);
      var s41 := Push2(s40, 0x0d46);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s175(s41, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 160
    * Starting at 0xd40
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xd46

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x593;
      assert s1.Peek(16) == 0x237;
      var s2 := Swap1(s1);
      var s3 := Push2(s2, 0x1250);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s4, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 255
    * Starting at 0x1250
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1250 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xd46

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x593;
      assert s1.Peek(16) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x125a);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0fb0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s6, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x125a

    requires s0.stack[5] == 0xd46

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x125a;
      assert s1.Peek(5) == 0xd46;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s9, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 256
    * Starting at 0x125a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd46

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1265);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0fb0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s7, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1265

    requires s0.stack[5] == 0xd46

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1265;
      assert s1.Peek(5) == 0xd46;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s9, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 257
    * Starting at 0x1265
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd46

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xd46;
      assert s11.Peek(9) == 0x8c1;
      assert s11.Peek(13) == 0x593;
      assert s11.Peek(18) == 0x237;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x127d);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s14, gas - 1)
      else
        ExecuteFromCFGNode_s181(s14, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 258
    * Starting at 0x1275
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1275 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd46

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x593

    requires s0.stack[17] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x127c);
      assert s1.Peek(0) == 0x127c;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Push2(s1, 0x1223);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s3, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 254
    * Starting at 0x1223
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1223 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x127c

    requires s0.stack[4] == 0xd46

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x127c;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 183
    * Segment Id for this node is: 260
    * Starting at 0x127d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd46

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x593

    requires s0.stack[17] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x593;
      assert s1.Peek(17) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s6, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 161
    * Starting at 0xd46
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x8c1

    requires s0.stack[9] == 0x593

    requires s0.stack[14] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x8c1;
      assert s1.Peek(9) == 0x593;
      assert s1.Peek(14) == 0x237;
      var s2 := Lt(s1);
      var s3 := Push2(s2, 0x0d6a);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s4, gas - 1)
      else
        ExecuteFromCFGNode_s185(s4, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 162
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push3(s0, 0x0bd223);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x593;
      assert s1.Peek(13) == 0x237;
      var s2 := Push2(s1, 0x09e3);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0d5d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1283);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s8, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 261
    * Starting at 0x1283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xd5d

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5d;
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x593;
      assert s1.Peek(16) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x128d);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0fb0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s6, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x128d

    requires s0.stack[5] == 0xd5d

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128d;
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s9, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 262
    * Starting at 0x128d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd5d

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd5d;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1298);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0fb0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s7, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1298

    requires s0.stack[5] == 0xd5d

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1298;
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s9, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 263
    * Starting at 0x1298
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1298 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd5d

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd5d;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Mul(s5);
      var s7 := Push2(s6, 0x12a6);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fb0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s10, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x12a6

    requires s0.stack[6] == 0xd5d

    requires s0.stack[11] == 0x8c1

    requires s0.stack[15] == 0x593

    requires s0.stack[20] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12a6;
      assert s1.Peek(6) == 0xd5d;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x593;
      assert s1.Peek(20) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s9, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 264
    * Starting at 0x12a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xd5d

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Div(s5);
      var s7 := Dup5(s6);
      var s8 := Eq(s7);
      var s9 := Dup4(s8);
      var s10 := IsZero(s9);
      var s11 := Or(s10);
      assert s11.Peek(5) == 0xd5d;
      assert s11.Peek(10) == 0x8c1;
      assert s11.Peek(14) == 0x593;
      assert s11.Peek(19) == 0x237;
      var s12 := Push2(s11, 0x12bd);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s13, gas - 1)
      else
        ExecuteFromCFGNode_s193(s13, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 265
    * Starting at 0x12b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd5d

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x12bc);
      assert s1.Peek(0) == 0x12bc;
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Push2(s1, 0x1223);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s3, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 254
    * Starting at 0x1223
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1223 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x12bc

    requires s0.stack[5] == 0xd5d

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12bc;
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 195
    * Segment Id for this node is: 267
    * Starting at 0x12bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd5d

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd5d;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s7, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 163
    * Starting at 0xd5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x8c1

    requires s0.stack[9] == 0x593

    requires s0.stack[14] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x8c1;
      assert s1.Peek(9) == 0x593;
      assert s1.Peek(14) == 0x237;
      var s2 := Push2(s1, 0x0d67);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x12f1);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s6, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 269
    * Starting at 0x12f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xd67

    requires s0.stack[6] == 0x8c1

    requires s0.stack[10] == 0x593

    requires s0.stack[15] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd67;
      assert s1.Peek(6) == 0x8c1;
      assert s1.Peek(10) == 0x593;
      assert s1.Peek(15) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x12fb);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0fb0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s6, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x12fb

    requires s0.stack[5] == 0xd67

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12fb;
      assert s1.Peek(5) == 0xd67;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s9, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 270
    * Starting at 0x12fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0xd67

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x593

    requires s0.stack[17] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd67;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x593;
      assert s1.Peek(17) == 0x237;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1306);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0fb0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s7, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x1306

    requires s0.stack[5] == 0xd67

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1306;
      assert s1.Peek(5) == 0xd67;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s9, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 271
    * Starting at 0x1306
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1306 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0xd67

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x593

    requires s0.stack[17] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd67;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x593;
      assert s1.Peek(17) == 0x237;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1316);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s6, gas - 1)
      else
        ExecuteFromCFGNode_s202(s6, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 272
    * Starting at 0x130e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x130e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xd67

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1315);
      assert s1.Peek(0) == 0x1315;
      assert s1.Peek(4) == 0xd67;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x593;
      assert s1.Peek(17) == 0x237;
      var s2 := Push2(s1, 0x12c4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s3, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 268
    * Starting at 0x12c4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x1315

    requires s0.stack[4] == 0xd67

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x593

    requires s0.stack[17] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1315;
      assert s1.Peek(4) == 0xd67;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x593;
      assert s1.Peek(17) == 0x237;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x12);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 204
    * Segment Id for this node is: 274
    * Starting at 0x1316
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1316 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xd67

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x593

    requires s0.stack[16] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd67;
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x593;
      assert s1.Peek(16) == 0x237;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Div(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s11, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 164
    * Starting at 0xd67
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x8c1

    requires s0.stack[8] == 0x593

    requires s0.stack[13] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x593;
      assert s1.Peek(13) == 0x237;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s206(s3, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 165
    * Starting at 0xd6a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Dup1(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x593;
      assert s11.Peek(15) == 0x237;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(6) == 0x8c1;
      assert s21.Peek(10) == 0x593;
      assert s21.Peek(15) == 0x237;
      var s22 := Dup3(s21);
      var s23 := Dup3(s22);
      var s24 := SLoad(s23);
      var s25 := Add(s24);
      var s26 := Swap3(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := SStore(s30);
      assert s31.Peek(4) == 0x8c1;
      assert s31.Peek(8) == 0x593;
      assert s31.Peek(13) == 0x237;
      var s32 := Pop(s31);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s156(s32, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 153
    * Starting at 0xba8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x593

    requires s0.stack[12] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x593;
      assert s1.Peek(12) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x593;
      assert s11.Peek(15) == 0x237;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x8c1;
      assert s21.Peek(9) == 0x593;
      assert s21.Peek(14) == 0x237;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0c31);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s29, gas - 1)
      else
        ExecuteFromCFGNode_s208(s29, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 154
    * Starting at 0xbf1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x8c1

    requires s0.stack[8] == 0x593

    requires s0.stack[13] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(5) == 0x8c1;
      assert s1.Peek(9) == 0x593;
      assert s1.Peek(14) == 0x237;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xe450d38c00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c28);
      assert s11.Peek(0) == 0xc28;
      assert s11.Peek(9) == 0x8c1;
      assert s11.Peek(13) == 0x593;
      assert s11.Peek(18) == 0x237;
      var s12 := Swap4(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x11ee);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s17, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 250
    * Starting at 0x11ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xc28

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x593

    requires s0.stack[18] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc28;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x593;
      assert s1.Peek(18) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1201);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1201;
      assert s11.Peek(7) == 0xc28;
      assert s11.Peek(12) == 0x8c1;
      assert s11.Peek(16) == 0x593;
      assert s11.Peek(21) == 0x237;
      var s12 := Dup7(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s14, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x1201

    requires s0.stack[8] == 0xc28

    requires s0.stack[13] == 0x8c1

    requires s0.stack[17] == 0x593

    requires s0.stack[22] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1201;
      assert s1.Peek(8) == 0xc28;
      assert s1.Peek(13) == 0x8c1;
      assert s1.Peek(17) == 0x593;
      assert s1.Peek(22) == 0x237;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s5, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x1201

    requires s0.stack[10] == 0xc28

    requires s0.stack[15] == 0x8c1

    requires s0.stack[19] == 0x593

    requires s0.stack[24] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x1201;
      assert s1.Peek(10) == 0xc28;
      assert s1.Peek(15) == 0x8c1;
      assert s1.Peek(19) == 0x593;
      assert s1.Peek(24) == 0x237;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s6, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x1201

    requires s0.stack[13] == 0xc28

    requires s0.stack[18] == 0x8c1

    requires s0.stack[22] == 0x593

    requires s0.stack[27] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x1201;
      assert s1.Peek(13) == 0xc28;
      assert s1.Peek(18) == 0x8c1;
      assert s1.Peek(22) == 0x593;
      assert s1.Peek(27) == 0x237;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s213(s11, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x1201

    requires s0.stack[12] == 0xc28

    requires s0.stack[17] == 0x8c1

    requires s0.stack[21] == 0x593

    requires s0.stack[26] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x1201;
      assert s1.Peek(12) == 0xc28;
      assert s1.Peek(17) == 0x8c1;
      assert s1.Peek(21) == 0x593;
      assert s1.Peek(26) == 0x237;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s7, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x1201

    requires s0.stack[9] == 0xc28

    requires s0.stack[14] == 0x8c1

    requires s0.stack[18] == 0x593

    requires s0.stack[23] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1201;
      assert s1.Peek(9) == 0xc28;
      assert s1.Peek(14) == 0x8c1;
      assert s1.Peek(18) == 0x593;
      assert s1.Peek(23) == 0x237;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s6, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 251
    * Starting at 0x1201
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1201 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xc28

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc28;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Push2(s1, 0x120e);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x1054);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s8, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x120e

    requires s0.stack[8] == 0xc28

    requires s0.stack[13] == 0x8c1

    requires s0.stack[17] == 0x593

    requires s0.stack[22] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x120e;
      assert s1.Peek(8) == 0xc28;
      assert s1.Peek(13) == 0x8c1;
      assert s1.Peek(17) == 0x593;
      assert s1.Peek(22) == 0x237;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s5, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x120e

    requires s0.stack[10] == 0xc28

    requires s0.stack[15] == 0x8c1

    requires s0.stack[19] == 0x593

    requires s0.stack[24] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x120e;
      assert s1.Peek(10) == 0xc28;
      assert s1.Peek(15) == 0x8c1;
      assert s1.Peek(19) == 0x593;
      assert s1.Peek(24) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s9, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x120e

    requires s0.stack[9] == 0xc28

    requires s0.stack[14] == 0x8c1

    requires s0.stack[18] == 0x593

    requires s0.stack[23] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x120e;
      assert s1.Peek(9) == 0xc28;
      assert s1.Peek(14) == 0x8c1;
      assert s1.Peek(18) == 0x593;
      assert s1.Peek(23) == 0x237;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s6, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 252
    * Starting at 0x120e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xc28

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc28;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Push2(s1, 0x121b);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x1054);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s8, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x121b

    requires s0.stack[8] == 0xc28

    requires s0.stack[13] == 0x8c1

    requires s0.stack[17] == 0x593

    requires s0.stack[22] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x121b;
      assert s1.Peek(8) == 0xc28;
      assert s1.Peek(13) == 0x8c1;
      assert s1.Peek(17) == 0x593;
      assert s1.Peek(22) == 0x237;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s5, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x121b

    requires s0.stack[10] == 0xc28

    requires s0.stack[15] == 0x8c1

    requires s0.stack[19] == 0x593

    requires s0.stack[24] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x121b;
      assert s1.Peek(10) == 0xc28;
      assert s1.Peek(15) == 0x8c1;
      assert s1.Peek(19) == 0x593;
      assert s1.Peek(24) == 0x237;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s9, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x121b

    requires s0.stack[9] == 0xc28

    requires s0.stack[14] == 0x8c1

    requires s0.stack[18] == 0x593

    requires s0.stack[23] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x121b;
      assert s1.Peek(9) == 0xc28;
      assert s1.Peek(14) == 0x8c1;
      assert s1.Peek(18) == 0x593;
      assert s1.Peek(23) == 0x237;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s6, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 253
    * Starting at 0x121b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xc28

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x593

    requires s0.stack[19] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc28;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x593;
      assert s1.Peek(19) == 0x237;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s8, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 155
    * Starting at 0xc28
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x8c1

    requires s0.stack[9] == 0x593

    requires s0.stack[14] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x8c1;
      assert s1.Peek(9) == 0x593;
      assert s1.Peek(14) == 0x237;
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

  /** Node 225
    * Segment Id for this node is: 156
    * Starting at 0xc31
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x8c1

    requires s0.stack[8] == 0x593

    requires s0.stack[13] == 0x237

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x593;
      assert s1.Peek(13) == 0x237;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push0(s4);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x8c1;
      assert s11.Peek(12) == 0x593;
      assert s11.Peek(17) == 0x237;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x8c1;
      assert s21.Peek(11) == 0x593;
      assert s21.Peek(16) == 0x237;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s154(s27, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 50
    * Starting at 0x1ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0207);
      var s3 := Push2(s2, 0x04ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s4, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 91
    * Starting at 0x4ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x207;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x05);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x04fb);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x11be);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s9, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 244
    * Starting at 0x11be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x4fb

    requires s0.stack[4] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4fb;
      assert s1.Peek(4) == 0x207;
      var s2 := Push0(s1);
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
      assert s11.Peek(7) == 0x207;
      var s12 := Push2(s11, 0x11d5);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s13, gas - 1)
      else
        ExecuteFromCFGNode_s229(s13, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 245
    * Starting at 0x11cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4fb

    requires s0.stack[6] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x4fb;
      assert s1.Peek(7) == 0x207;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s230(s5, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 246
    * Starting at 0x11d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4fb

    requires s0.stack[6] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4fb;
      assert s1.Peek(6) == 0x207;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x11e8);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s8, gas - 1)
      else
        ExecuteFromCFGNode_s231(s8, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 247
    * Starting at 0x11e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4fb

    requires s0.stack[6] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x11e7);
      assert s1.Peek(0) == 0x11e7;
      assert s1.Peek(4) == 0x4fb;
      assert s1.Peek(7) == 0x207;
      var s2 := Push2(s1, 0x1191);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s3, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 243
    * Starting at 0x1191
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x11e7

    requires s0.stack[4] == 0x4fb

    requires s0.stack[7] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11e7;
      assert s1.Peek(4) == 0x4fb;
      assert s1.Peek(7) == 0x207;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 233
    * Segment Id for this node is: 249
    * Starting at 0x11e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4fb

    requires s0.stack[6] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4fb;
      assert s1.Peek(6) == 0x207;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s6, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 92
    * Starting at 0x4fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x207;
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
      assert s11.Peek(4) == 0x207;
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
      assert s21.Peek(5) == 0x207;
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
      assert s31.Peek(8) == 0x207;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x11be);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s34, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 244
    * Starting at 0x11be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x527

    requires s0.stack[8] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x527;
      assert s1.Peek(8) == 0x207;
      var s2 := Push0(s1);
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
      assert s11.Peek(11) == 0x207;
      var s12 := Push2(s11, 0x11d5);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s237(s13, gas - 1)
      else
        ExecuteFromCFGNode_s236(s13, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 245
    * Starting at 0x11cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x527

    requires s0.stack[10] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x527;
      assert s1.Peek(11) == 0x207;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s237(s5, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 246
    * Starting at 0x11d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x527

    requires s0.stack[10] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x527;
      assert s1.Peek(10) == 0x207;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x11e8);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s8, gas - 1)
      else
        ExecuteFromCFGNode_s238(s8, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 247
    * Starting at 0x11e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x527

    requires s0.stack[10] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x11e7);
      assert s1.Peek(0) == 0x11e7;
      assert s1.Peek(4) == 0x527;
      assert s1.Peek(11) == 0x207;
      var s2 := Push2(s1, 0x1191);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s3, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 243
    * Starting at 0x1191
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x11e7

    requires s0.stack[4] == 0x527

    requires s0.stack[11] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11e7;
      assert s1.Peek(4) == 0x527;
      assert s1.Peek(11) == 0x207;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 240
    * Segment Id for this node is: 249
    * Starting at 0x11e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x527

    requires s0.stack[10] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x527;
      assert s1.Peek(10) == 0x207;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s6, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 93
    * Starting at 0x527
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x527 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x207;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0572);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s244(s5, gas - 1)
      else
        ExecuteFromCFGNode_s242(s5, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 94
    * Starting at 0x52e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x207;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0549);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s5, gas - 1)
      else
        ExecuteFromCFGNode_s243(s5, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 95
    * Starting at 0x536
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x207;
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
      assert s11.Peek(7) == 0x207;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0572);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s14, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 99
    * Starting at 0x572
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x572 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x207;
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
      ExecuteFromCFGNode_s245(s10, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 51
    * Starting at 0x207
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0214);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0f32);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s8, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 182
    * Starting at 0xf32
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf32 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x214;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(5) == 0x214;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0f4a);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0efa);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s19, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 177
    * Starting at 0xefa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xf4a

    requires s0.stack[6] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf4a;
      assert s1.Peek(6) == 0x214;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f04);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0ea8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s6, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 170
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xf04

    requires s0.stack[5] == 0xf4a

    requires s0.stack[9] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf04;
      assert s1.Peek(5) == 0xf4a;
      assert s1.Peek(9) == 0x214;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s10, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 178
    * Starting at 0xf04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xf4a

    requires s0.stack[8] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf4a;
      assert s1.Peek(8) == 0x214;
      var s2 := Push2(s1, 0x0f0e);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0eb2);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s6, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 171
    * Starting at 0xeb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xf0e

    requires s0.stack[7] == 0xf4a

    requires s0.stack[11] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf0e;
      assert s1.Peek(7) == 0xf4a;
      assert s1.Peek(11) == 0x214;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xf0e;
      assert s11.Peek(8) == 0xf4a;
      assert s11.Peek(12) == 0x214;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s15, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 179
    * Starting at 0xf0e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xf4a

    requires s0.stack[9] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf4a;
      assert s1.Peek(9) == 0x214;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0f1e);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0ec2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s11, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 172
    * Starting at 0xec2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xf1e

    requires s0.stack[8] == 0xf4a

    requires s0.stack[12] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf1e;
      assert s1.Peek(8) == 0xf4a;
      assert s1.Peek(12) == 0x214;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s253(s2, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 173
    * Starting at 0xec4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xf1e

    requires s0.stack[9] == 0xf4a

    requires s0.stack[13] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf1e;
      assert s1.Peek(9) == 0xf4a;
      assert s1.Peek(13) == 0x214;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0edf);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s7, gas - 1)
      else
        ExecuteFromCFGNode_s254(s7, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 174
    * Starting at 0xecd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xf1e

    requires s0.stack[9] == 0xf4a

    requires s0.stack[13] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xf1e;
      assert s1.Peek(10) == 0xf4a;
      assert s1.Peek(14) == 0x214;
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
      assert s11.Peek(5) == 0xf1e;
      assert s11.Peek(10) == 0xf4a;
      assert s11.Peek(14) == 0x214;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0ec4);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s15, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 175
    * Starting at 0xedf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xf1e

    requires s0.stack[9] == 0xf4a

    requires s0.stack[13] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf1e;
      assert s1.Peek(9) == 0xf4a;
      assert s1.Peek(13) == 0x214;
      var s2 := Push0(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s11, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 180
    * Starting at 0xf1e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xf4a

    requires s0.stack[8] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf4a;
      assert s1.Peek(8) == 0x214;
      var s2 := Push2(s1, 0x0f27);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0eea);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s5, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 176
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xf27

    requires s0.stack[6] == 0xf4a

    requires s0.stack[10] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf27;
      assert s1.Peek(6) == 0xf4a;
      assert s1.Peek(10) == 0x214;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xf27;
      assert s11.Peek(7) == 0xf4a;
      assert s11.Peek(11) == 0x214;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s14, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 181
    * Starting at 0xf27
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xf4a

    requires s0.stack[9] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf4a;
      assert s1.Peek(9) == 0x214;
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
      ExecuteFromCFGNode_s259(s11, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 183
    * Starting at 0xf4a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x214

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x214;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s8, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 52
    * Starting at 0x214
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x214 as nat
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

  /** Node 261
    * Segment Id for this node is: 96
    * Starting at 0x549
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x549 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x207;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Push0(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push0(s8);
      var s10 := Keccak256(s9);
      var s11 := Swap1(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s262(s11, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 97
    * Starting at 0x555
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x555 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x207;
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
      assert s11.Peek(7) == 0x207;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x0555);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s262(s16, gas - 1)
      else
        ExecuteFromCFGNode_s263(s16, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 98
    * Starting at 0x569
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x569 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x207

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x207;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s244(s8, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 10
    * Starting at 0x64
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64 as nat
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
      var s5 := Push2(s4, 0x01a7);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s303(s6, gas - 1)
      else
        ExecuteFromCFGNode_s265(s6, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 11
    * Starting at 0x70
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01d7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s279(s5, gas - 1)
      else
        ExecuteFromCFGNode_s266(s5, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 12
    * Starting at 0x7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
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
        ExecuteFromCFGNode_s268(s5, gas - 1)
      else
        ExecuteFromCFGNode_s267(s5, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 13
    * Starting at 0x86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00cd);
      assert s1.Peek(0) == 0xcd;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 47
    * Starting at 0x1e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e9);
      var s3 := Push2(s2, 0x04c4);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s4, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 90
    * Starting at 0x4c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e9;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x07);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x1e9;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s17, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 48
    * Starting at 0x1e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01f6);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s8, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1f6;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x1f6;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s14, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x1f6;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s5, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x1f6;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s6, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x1f6;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s275(s11, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x1f6;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s7, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x1f6;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s6, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1f6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s6, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 49
    * Starting at 0x1f6
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f6 as nat
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

  /** Node 279
    * Segment Id for this node is: 45
    * Starting at 0x1d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01df);
      var s3 := Push2(s2, 0x04b1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s4, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 87
    * Starting at 0x4b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1df;
      var s2 := Push2(s1, 0x04b9);
      var s3 := Push2(s2, 0x06bd);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s4, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 114
    * Starting at 0x6bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b9

    requires s0.stack[1] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4b9;
      assert s1.Peek(1) == 0x1df;
      var s2 := Push2(s1, 0x06c5);
      var s3 := Push2(s2, 0x06a4);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s4, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x6c5

    requires s0.stack[1] == 0x4b9

    requires s0.stack[2] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6c5;
      assert s1.Peek(1) == 0x4b9;
      assert s1.Peek(2) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s7, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 115
    * Starting at 0x6c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4b9

    requires s0.stack[2] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b9;
      assert s1.Peek(2) == 0x1df;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x06e3);
      var s5 := Push2(s4, 0x04c4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s6, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 90
    * Starting at 0x4c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x6e3

    requires s0.stack[2] == 0x4b9

    requires s0.stack[3] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6e3;
      assert s1.Peek(2) == 0x4b9;
      assert s1.Peek(3) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x07);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x6e3;
      assert s11.Peek(4) == 0x4b9;
      assert s11.Peek(5) == 0x1df;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s17, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 116
    * Starting at 0x6e3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x4b9

    requires s0.stack[3] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4b9;
      assert s1.Peek(3) == 0x1df;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0742);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s297(s6, gas - 1)
      else
        ExecuteFromCFGNode_s286(s6, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 117
    * Starting at 0x6ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b9

    requires s0.stack[1] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0706);
      assert s1.Peek(0) == 0x706;
      assert s1.Peek(1) == 0x4b9;
      assert s1.Peek(2) == 0x1df;
      var s2 := Push2(s1, 0x06a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s3, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x706

    requires s0.stack[1] == 0x4b9

    requires s0.stack[2] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x706;
      assert s1.Peek(1) == 0x4b9;
      assert s1.Peek(2) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s7, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 118
    * Starting at 0x706
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x706 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4b9

    requires s0.stack[2] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b9;
      assert s1.Peek(2) == 0x1df;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0739);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x739;
      assert s11.Peek(3) == 0x4b9;
      assert s11.Peek(4) == 0x1df;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s13, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x739

    requires s0.stack[3] == 0x4b9

    requires s0.stack[4] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x739;
      assert s1.Peek(3) == 0x4b9;
      assert s1.Peek(4) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x739;
      assert s11.Peek(6) == 0x4b9;
      assert s11.Peek(7) == 0x1df;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s290(s14, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x739

    requires s0.stack[7] == 0x4b9

    requires s0.stack[8] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x739;
      assert s1.Peek(7) == 0x4b9;
      assert s1.Peek(8) == 0x1df;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s5, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x739

    requires s0.stack[9] == 0x4b9

    requires s0.stack[10] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x739;
      assert s1.Peek(9) == 0x4b9;
      assert s1.Peek(10) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s6, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x739

    requires s0.stack[12] == 0x4b9

    requires s0.stack[13] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x739;
      assert s1.Peek(12) == 0x4b9;
      assert s1.Peek(13) == 0x1df;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s293(s11, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x739

    requires s0.stack[11] == 0x4b9

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x739;
      assert s1.Peek(11) == 0x4b9;
      assert s1.Peek(12) == 0x1df;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s294(s7, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x739

    requires s0.stack[8] == 0x4b9

    requires s0.stack[9] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x739;
      assert s1.Peek(8) == 0x4b9;
      assert s1.Peek(9) == 0x1df;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s6, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x739

    requires s0.stack[4] == 0x4b9

    requires s0.stack[5] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x739;
      assert s1.Peek(4) == 0x4b9;
      assert s1.Peek(5) == 0x1df;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s6, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 119
    * Starting at 0x739
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4b9

    requires s0.stack[2] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b9;
      assert s1.Peek(2) == 0x1df;
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

  /** Node 297
    * Segment Id for this node is: 120
    * Starting at 0x742
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x742 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b9

    requires s0.stack[1] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4b9;
      assert s1.Peek(1) == 0x1df;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s298(s2, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 88
    * Starting at 0x4b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1df;
      var s2 := Push2(s1, 0x04c2);
      var s3 := Push0(s2);
      var s4 := Push2(s3, 0x08c6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s5, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 137
    * Starting at 0x8c6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4c2

    requires s0.stack[2] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4c2;
      assert s1.Peek(2) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x07);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x4c2;
      assert s11.Peek(4) == 0x1df;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x07);
      var s18 := Push0(s17);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x4c2;
      assert s21.Peek(7) == 0x1df;
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
      assert s31.Peek(7) == 0x4c2;
      assert s31.Peek(8) == 0x1df;
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
      ExecuteFromCFGNode_s300(s41, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 138
    * Starting at 0x959
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x959 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x4c2

    requires s0.stack[6] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x4c2;
      assert s1.Peek(5) == 0x1df;
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
      assert s11.Peek(2) == 0x4c2;
      assert s11.Peek(3) == 0x1df;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s14, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 89
    * Starting at 0x4c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1df;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s2, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 46
    * Starting at 0x1df
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1df as nat
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

  /** Node 303
    * Segment Id for this node is: 41
    * Starting at 0x1a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01c1);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01bc);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1bc;
      assert s11.Peek(3) == 0x1c1;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x107c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s14, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 216
    * Starting at 0x107c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1bc

    requires s0.stack[3] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1bc;
      assert s1.Peek(3) == 0x1c1;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1091);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s307(s10, gas - 1)
      else
        ExecuteFromCFGNode_s305(s10, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 217
    * Starting at 0x1089
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1089 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1bc

    requires s0.stack[4] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1090);
      assert s1.Peek(0) == 0x1090;
      assert s1.Peek(4) == 0x1bc;
      assert s1.Peek(5) == 0x1c1;
      var s2 := Push2(s1, 0x0f52);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s3, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 184
    * Starting at 0xf52
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x1090

    requires s0.stack[4] == 0x1bc

    requires s0.stack[5] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1090;
      assert s1.Peek(4) == 0x1bc;
      assert s1.Peek(5) == 0x1c1;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 307
    * Segment Id for this node is: 219
    * Starting at 0x1091
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1091 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1bc

    requires s0.stack[4] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1bc;
      assert s1.Peek(4) == 0x1c1;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x109e);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0f9c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s9, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x109e

    requires s0.stack[7] == 0x1bc

    requires s0.stack[8] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109e;
      assert s1.Peek(7) == 0x1bc;
      assert s1.Peek(8) == 0x1c1;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s10, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x1bc

    requires s0.stack[11] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x109e;
      assert s1.Peek(10) == 0x1bc;
      assert s1.Peek(11) == 0x1c1;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s5, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x109e

    requires s0.stack[12] == 0x1bc

    requires s0.stack[13] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x109e;
      assert s1.Peek(12) == 0x1bc;
      assert s1.Peek(13) == 0x1c1;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s6, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x109e

    requires s0.stack[15] == 0x1bc

    requires s0.stack[16] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x109e;
      assert s1.Peek(15) == 0x1bc;
      assert s1.Peek(16) == 0x1c1;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s312(s11, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x109e

    requires s0.stack[14] == 0x1bc

    requires s0.stack[15] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x109e;
      assert s1.Peek(14) == 0x1bc;
      assert s1.Peek(15) == 0x1c1;
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
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x109e

    requires s0.stack[11] == 0x1bc

    requires s0.stack[12] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x109e;
      assert s1.Peek(11) == 0x1bc;
      assert s1.Peek(12) == 0x1c1;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s315(s5, gas - 1)
      else
        ExecuteFromCFGNode_s314(s5, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x1bc

    requires s0.stack[11] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x109e;
      assert s1.Peek(11) == 0x1bc;
      assert s1.Peek(12) == 0x1c1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 315
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x1bc

    requires s0.stack[11] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x109e;
      assert s1.Peek(10) == 0x1bc;
      assert s1.Peek(11) == 0x1c1;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s3, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x109e

    requires s0.stack[8] == 0x1bc

    requires s0.stack[9] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x109e;
      assert s1.Peek(8) == 0x1bc;
      assert s1.Peek(9) == 0x1c1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s317(s6, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 220
    * Starting at 0x109e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1bc

    requires s0.stack[6] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1bc;
      assert s1.Peek(6) == 0x1c1;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s9, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 42
    * Starting at 0x1bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1c1;
      var s2 := Push2(s1, 0x046c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s319(s3, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 86
    * Starting at 0x46c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1c1;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x1c1;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(3) == 0x1c1;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Swap2(s23);
      var s25 := Swap1(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s27, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 43
    * Starting at 0x1c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01ce);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1063);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s8, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 214
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ce;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1076);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1076;
      assert s11.Peek(5) == 0x1ce;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x1054);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s322(s14, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1076

    requires s0.stack[6] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1076;
      assert s1.Peek(6) == 0x1ce;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s5, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x1076

    requires s0.stack[8] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x1076;
      assert s1.Peek(8) == 0x1ce;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s324(s9, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1076

    requires s0.stack[7] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1076;
      assert s1.Peek(7) == 0x1ce;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s6, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 215
    * Starting at 0x1076
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1076 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1ce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ce;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s6, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 44
    * Starting at 0x1ce
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
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
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 327
    * Segment Id for this node is: 14
    * Starting at 0x8a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a as nat
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
      var s5 := Push2(s4, 0x00d1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s653(s6, gas - 1)
      else
        ExecuteFromCFGNode_s328(s6, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 15
    * Starting at 0x96
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00ef);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s584(s5, gas - 1)
      else
        ExecuteFromCFGNode_s329(s5, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 16
    * Starting at 0xa1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x011f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s575(s5, gas - 1)
      else
        ExecuteFromCFGNode_s330(s5, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 17
    * Starting at 0xac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x19ab453c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x013d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s539(s5, gas - 1)
      else
        ExecuteFromCFGNode_s331(s5, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 18
    * Starting at 0xb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0159);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s342(s5, gas - 1)
      else
        ExecuteFromCFGNode_s332(s5, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 19
    * Starting at 0xc2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0189);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s333(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 38
    * Starting at 0x189
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x189 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0191);
      var s3 := Push2(s2, 0x0464);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s4, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 85
    * Starting at 0x464
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x464 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x191

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x191;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x12);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s7, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 39
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x019e);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1112);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s8, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 231
    * Starting at 0x1112
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1112 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x19e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x19e;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1125);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1125;
      assert s11.Peek(5) == 0x19e;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x1103);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s14, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 229
    * Starting at 0x1103
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1103 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1125

    requires s0.stack[6] == 0x19e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1125;
      assert s1.Peek(6) == 0x19e;
      var s2 := Push2(s1, 0x110c);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x10f7);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s338(s5, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 228
    * Starting at 0x10f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x110c

    requires s0.stack[4] == 0x1125

    requires s0.stack[8] == 0x19e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x110c;
      assert s1.Peek(4) == 0x1125;
      assert s1.Peek(8) == 0x19e;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s339(s11, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 230
    * Starting at 0x110c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1125

    requires s0.stack[7] == 0x19e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1125;
      assert s1.Peek(7) == 0x19e;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s340(s6, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 232
    * Starting at 0x1125
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1125 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x19e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x19e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s6, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 40
    * Starting at 0x19e
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
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
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 342
    * Segment Id for this node is: 34
    * Starting at 0x159
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x159 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0173);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x016e);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x16e;
      assert s11.Peek(3) == 0x173;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x10a7);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s343(s14, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 221
    * Starting at 0x10a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x16e

    requires s0.stack[3] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16e;
      assert s1.Peek(3) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x10be);
      assert s11.Peek(0) == 0x10be;
      assert s11.Peek(7) == 0x16e;
      assert s11.Peek(8) == 0x173;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s346(s12, gas - 1)
      else
        ExecuteFromCFGNode_s344(s12, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 222
    * Starting at 0x10b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x16e

    requires s0.stack[6] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10bd);
      assert s1.Peek(0) == 0x10bd;
      assert s1.Peek(6) == 0x16e;
      assert s1.Peek(7) == 0x173;
      var s2 := Push2(s1, 0x0f52);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s3, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 184
    * Starting at 0xf52
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x10bd

    requires s0.stack[6] == 0x16e

    requires s0.stack[7] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10bd;
      assert s1.Peek(6) == 0x16e;
      assert s1.Peek(7) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 346
    * Segment Id for this node is: 224
    * Starting at 0x10be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x16e

    requires s0.stack[6] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x16e;
      assert s1.Peek(6) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x10cb);
      var s4 := Dup7(s3);
      var s5 := Dup3(s4);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0f9c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s9, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x10cb

    requires s0.stack[9] == 0x16e

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10cb;
      assert s1.Peek(9) == 0x16e;
      assert s1.Peek(10) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s348(s10, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x10cb

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x10cb;
      assert s1.Peek(12) == 0x16e;
      assert s1.Peek(13) == 0x173;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s349(s5, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x10cb

    requires s0.stack[14] == 0x16e

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x10cb;
      assert s1.Peek(14) == 0x16e;
      assert s1.Peek(15) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s6, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x10cb

    requires s0.stack[17] == 0x16e

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x10cb;
      assert s1.Peek(17) == 0x16e;
      assert s1.Peek(18) == 0x173;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s351(s11, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x10cb

    requires s0.stack[16] == 0x16e

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x10cb;
      assert s1.Peek(16) == 0x16e;
      assert s1.Peek(17) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s7, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x10cb

    requires s0.stack[13] == 0x16e

    requires s0.stack[14] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x10cb;
      assert s1.Peek(13) == 0x16e;
      assert s1.Peek(14) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s354(s5, gas - 1)
      else
        ExecuteFromCFGNode_s353(s5, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x10cb

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x10cb;
      assert s1.Peek(13) == 0x16e;
      assert s1.Peek(14) == 0x173;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 354
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x10cb

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x10cb;
      assert s1.Peek(12) == 0x16e;
      assert s1.Peek(13) == 0x173;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s3, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x10cb

    requires s0.stack[10] == 0x16e

    requires s0.stack[11] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10cb;
      assert s1.Peek(10) == 0x16e;
      assert s1.Peek(11) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s6, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 225
    * Starting at 0x10cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x16e

    requires s0.stack[8] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x16e;
      assert s1.Peek(8) == 0x173;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x10dc);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0f9c);
      assert s11.Peek(0) == 0xf9c;
      assert s11.Peek(3) == 0x10dc;
      assert s11.Peek(10) == 0x16e;
      assert s11.Peek(11) == 0x173;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s12, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x10dc

    requires s0.stack[9] == 0x16e

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10dc;
      assert s1.Peek(9) == 0x16e;
      assert s1.Peek(10) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s10, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x10dc

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x10dc;
      assert s1.Peek(12) == 0x16e;
      assert s1.Peek(13) == 0x173;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s359(s5, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x10dc

    requires s0.stack[14] == 0x16e

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x10dc;
      assert s1.Peek(14) == 0x16e;
      assert s1.Peek(15) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s6, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x10dc

    requires s0.stack[17] == 0x16e

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x10dc;
      assert s1.Peek(17) == 0x16e;
      assert s1.Peek(18) == 0x173;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s361(s11, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x10dc

    requires s0.stack[16] == 0x16e

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x10dc;
      assert s1.Peek(16) == 0x16e;
      assert s1.Peek(17) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s7, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x10dc

    requires s0.stack[13] == 0x16e

    requires s0.stack[14] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x10dc;
      assert s1.Peek(13) == 0x16e;
      assert s1.Peek(14) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s364(s5, gas - 1)
      else
        ExecuteFromCFGNode_s363(s5, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x10dc

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x10dc;
      assert s1.Peek(13) == 0x16e;
      assert s1.Peek(14) == 0x173;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 364
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x10dc

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x10dc;
      assert s1.Peek(12) == 0x16e;
      assert s1.Peek(13) == 0x173;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s3, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x10dc

    requires s0.stack[10] == 0x16e

    requires s0.stack[11] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10dc;
      assert s1.Peek(10) == 0x16e;
      assert s1.Peek(11) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s366(s6, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 226
    * Starting at 0x10dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x16e

    requires s0.stack[8] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x16e;
      assert s1.Peek(8) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Push2(s5, 0x10ed);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0fcf);
      assert s11.Peek(0) == 0xfcf;
      assert s11.Peek(3) == 0x10ed;
      assert s11.Peek(10) == 0x16e;
      assert s11.Peek(11) == 0x173;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s367(s12, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 199
    * Starting at 0xfcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x10ed

    requires s0.stack[9] == 0x16e

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ed;
      assert s1.Peek(9) == 0x16e;
      assert s1.Peek(10) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0fdd);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fb9);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s10, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 195
    * Starting at 0xfb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x10ed

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfdd;
      assert s1.Peek(5) == 0x10ed;
      assert s1.Peek(12) == 0x16e;
      assert s1.Peek(13) == 0x173;
      var s2 := Push2(s1, 0x0fc2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s5, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xfc2

    requires s0.stack[3] == 0xfdd

    requires s0.stack[7] == 0x10ed

    requires s0.stack[14] == 0x16e

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfc2;
      assert s1.Peek(3) == 0xfdd;
      assert s1.Peek(7) == 0x10ed;
      assert s1.Peek(14) == 0x16e;
      assert s1.Peek(15) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s9, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 196
    * Starting at 0xfc2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xfdd

    requires s0.stack[6] == 0x10ed

    requires s0.stack[13] == 0x16e

    requires s0.stack[14] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfdd;
      assert s1.Peek(6) == 0x10ed;
      assert s1.Peek(13) == 0x16e;
      assert s1.Peek(14) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0fcc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s372(s5, gas - 1)
      else
        ExecuteFromCFGNode_s371(s5, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 197
    * Starting at 0xfc9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x10ed

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfdd;
      assert s1.Peek(6) == 0x10ed;
      assert s1.Peek(13) == 0x16e;
      assert s1.Peek(14) == 0x173;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 372
    * Segment Id for this node is: 198
    * Starting at 0xfcc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x10ed

    requires s0.stack[12] == 0x16e

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfdd;
      assert s1.Peek(5) == 0x10ed;
      assert s1.Peek(12) == 0x16e;
      assert s1.Peek(13) == 0x173;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s3, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 200
    * Starting at 0xfdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x10ed

    requires s0.stack[10] == 0x16e

    requires s0.stack[11] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10ed;
      assert s1.Peek(10) == 0x16e;
      assert s1.Peek(11) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s6, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 227
    * Starting at 0x10ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x16e

    requires s0.stack[8] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x16e;
      assert s1.Peek(8) == 0x173;
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
      ExecuteFromCFGNode_s375(s10, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 35
    * Starting at 0x16e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x173;
      var s2 := Push2(s1, 0x0436);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s376(s3, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 81
    * Starting at 0x436
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x436 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0440);
      var s5 := Push2(s4, 0x06a4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s6, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x440

    requires s0.stack[6] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x440;
      assert s1.Peek(6) == 0x173;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s7, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 82
    * Starting at 0x440
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x440 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x044d);
      var s5 := Dup6(s4);
      var s6 := Dup3(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x0744);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s9, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 121
    * Starting at 0x744
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x744 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x44d

    requires s0.stack[9] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x44d;
      assert s1.Peek(9) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x074f);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x059e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s7, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 103
    * Starting at 0x59e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x74f

    requires s0.stack[7] == 0x44d

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x74f;
      assert s1.Peek(7) == 0x44d;
      assert s1.Peek(13) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x74f;
      assert s11.Peek(10) == 0x44d;
      assert s11.Peek(16) == 0x173;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(5) == 0x74f;
      assert s21.Peek(10) == 0x44d;
      assert s21.Peek(16) == 0x173;
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
      assert s31.Peek(5) == 0x74f;
      assert s31.Peek(10) == 0x44d;
      assert s31.Peek(16) == 0x173;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s381(s41, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 104
    * Starting at 0x61c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x74f

    requires s0.stack[8] == 0x44d

    requires s0.stack[14] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x74f;
      assert s1.Peek(8) == 0x44d;
      assert s1.Peek(14) == 0x173;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s4, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 122
    * Starting at 0x74f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x44d

    requires s0.stack[11] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x44d;
      assert s1.Peek(11) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x07d0);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s433(s8, gas - 1)
      else
        ExecuteFromCFGNode_s383(s8, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 123
    * Starting at 0x779
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x779 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x44d

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x44d;
      assert s1.Peek(11) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x07c1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s401(s6, gas - 1)
      else
        ExecuteFromCFGNode_s384(s6, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 124
    * Starting at 0x781
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x781 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x44d

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(5) == 0x44d;
      assert s1.Peek(11) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xfb8f41b200000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x07b8);
      assert s11.Peek(0) == 0x7b8;
      assert s11.Peek(9) == 0x44d;
      assert s11.Peek(15) == 0x173;
      var s12 := Swap4(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x11ee);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s17, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 250
    * Starting at 0x11ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7b8

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7b8;
      assert s1.Peek(9) == 0x44d;
      assert s1.Peek(15) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1201);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1201;
      assert s11.Peek(7) == 0x7b8;
      assert s11.Peek(12) == 0x44d;
      assert s11.Peek(18) == 0x173;
      var s12 := Dup7(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s14, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1201

    requires s0.stack[8] == 0x7b8

    requires s0.stack[13] == 0x44d

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1201;
      assert s1.Peek(8) == 0x7b8;
      assert s1.Peek(13) == 0x44d;
      assert s1.Peek(19) == 0x173;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s5, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x1201

    requires s0.stack[10] == 0x7b8

    requires s0.stack[15] == 0x44d

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x1201;
      assert s1.Peek(10) == 0x7b8;
      assert s1.Peek(15) == 0x44d;
      assert s1.Peek(21) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s388(s6, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x1201

    requires s0.stack[13] == 0x7b8

    requires s0.stack[18] == 0x44d

    requires s0.stack[24] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x1201;
      assert s1.Peek(13) == 0x7b8;
      assert s1.Peek(18) == 0x44d;
      assert s1.Peek(24) == 0x173;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s389(s11, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x1201

    requires s0.stack[12] == 0x7b8

    requires s0.stack[17] == 0x44d

    requires s0.stack[23] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x1201;
      assert s1.Peek(12) == 0x7b8;
      assert s1.Peek(17) == 0x44d;
      assert s1.Peek(23) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s7, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1201

    requires s0.stack[9] == 0x7b8

    requires s0.stack[14] == 0x44d

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1201;
      assert s1.Peek(9) == 0x7b8;
      assert s1.Peek(14) == 0x44d;
      assert s1.Peek(20) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s391(s6, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 251
    * Starting at 0x1201
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1201 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x7b8

    requires s0.stack[10] == 0x44d

    requires s0.stack[16] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7b8;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
      var s2 := Push2(s1, 0x120e);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x1054);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s8, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x120e

    requires s0.stack[8] == 0x7b8

    requires s0.stack[13] == 0x44d

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x120e;
      assert s1.Peek(8) == 0x7b8;
      assert s1.Peek(13) == 0x44d;
      assert s1.Peek(19) == 0x173;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s5, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x120e

    requires s0.stack[10] == 0x7b8

    requires s0.stack[15] == 0x44d

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x120e;
      assert s1.Peek(10) == 0x7b8;
      assert s1.Peek(15) == 0x44d;
      assert s1.Peek(21) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s9, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x120e

    requires s0.stack[9] == 0x7b8

    requires s0.stack[14] == 0x44d

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x120e;
      assert s1.Peek(9) == 0x7b8;
      assert s1.Peek(14) == 0x44d;
      assert s1.Peek(20) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s6, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 252
    * Starting at 0x120e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x7b8

    requires s0.stack[10] == 0x44d

    requires s0.stack[16] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7b8;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
      var s2 := Push2(s1, 0x121b);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x1054);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s8, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x121b

    requires s0.stack[8] == 0x7b8

    requires s0.stack[13] == 0x44d

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x121b;
      assert s1.Peek(8) == 0x7b8;
      assert s1.Peek(13) == 0x44d;
      assert s1.Peek(19) == 0x173;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s5, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x121b

    requires s0.stack[10] == 0x7b8

    requires s0.stack[15] == 0x44d

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x121b;
      assert s1.Peek(10) == 0x7b8;
      assert s1.Peek(15) == 0x44d;
      assert s1.Peek(21) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s9, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x121b

    requires s0.stack[9] == 0x7b8

    requires s0.stack[14] == 0x44d

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x121b;
      assert s1.Peek(9) == 0x7b8;
      assert s1.Peek(14) == 0x44d;
      assert s1.Peek(20) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s399(s6, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 253
    * Starting at 0x121b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x7b8

    requires s0.stack[10] == 0x44d

    requires s0.stack[16] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7b8;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s400(s8, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 125
    * Starting at 0x7b8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x44d

    requires s0.stack[11] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x44d;
      assert s1.Peek(11) == 0x173;
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

  /** Node 401
    * Segment Id for this node is: 126
    * Starting at 0x7c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x44d

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x44d;
      assert s1.Peek(10) == 0x173;
      var s2 := Push2(s1, 0x07cf);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Sub(s6);
      var s8 := Push0(s7);
      var s9 := Push2(s8, 0x0989);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s402(s10, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 139
    * Starting at 0x989
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x989 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7cf

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7cf;
      assert s1.Peek(9) == 0x44d;
      assert s1.Peek(15) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x09f9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s412(s10, gas - 1)
      else
        ExecuteFromCFGNode_s403(s10, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 140
    * Starting at 0x9bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7cf

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x7cf;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xe602df0500000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x09f0);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x9f0;
      assert s11.Peek(7) == 0x7cf;
      assert s11.Peek(12) == 0x44d;
      assert s11.Peek(18) == 0x173;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s13, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x9f0

    requires s0.stack[7] == 0x7cf

    requires s0.stack[12] == 0x44d

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9f0;
      assert s1.Peek(7) == 0x7cf;
      assert s1.Peek(12) == 0x44d;
      assert s1.Peek(18) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x9f0;
      assert s11.Peek(10) == 0x7cf;
      assert s11.Peek(15) == 0x44d;
      assert s11.Peek(21) == 0x173;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s14, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x9f0

    requires s0.stack[11] == 0x7cf

    requires s0.stack[16] == 0x44d

    requires s0.stack[22] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x9f0;
      assert s1.Peek(11) == 0x7cf;
      assert s1.Peek(16) == 0x44d;
      assert s1.Peek(22) == 0x173;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s5, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x9f0

    requires s0.stack[13] == 0x7cf

    requires s0.stack[18] == 0x44d

    requires s0.stack[24] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x9f0;
      assert s1.Peek(13) == 0x7cf;
      assert s1.Peek(18) == 0x44d;
      assert s1.Peek(24) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s6, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x9f0

    requires s0.stack[16] == 0x7cf

    requires s0.stack[21] == 0x44d

    requires s0.stack[27] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x9f0;
      assert s1.Peek(16) == 0x7cf;
      assert s1.Peek(21) == 0x44d;
      assert s1.Peek(27) == 0x173;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s408(s11, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x9f0

    requires s0.stack[15] == 0x7cf

    requires s0.stack[20] == 0x44d

    requires s0.stack[26] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x9f0;
      assert s1.Peek(15) == 0x7cf;
      assert s1.Peek(20) == 0x44d;
      assert s1.Peek(26) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s409(s7, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x9f0

    requires s0.stack[12] == 0x7cf

    requires s0.stack[17] == 0x44d

    requires s0.stack[23] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x9f0;
      assert s1.Peek(12) == 0x7cf;
      assert s1.Peek(17) == 0x44d;
      assert s1.Peek(23) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s6, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x9f0

    requires s0.stack[8] == 0x7cf

    requires s0.stack[13] == 0x44d

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9f0;
      assert s1.Peek(8) == 0x7cf;
      assert s1.Peek(13) == 0x44d;
      assert s1.Peek(19) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s6, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 141
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x7cf

    requires s0.stack[10] == 0x44d

    requires s0.stack[16] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7cf;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
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

  /** Node 412
    * Segment Id for this node is: 142
    * Starting at 0x9f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7cf

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7cf;
      assert s1.Peek(9) == 0x44d;
      assert s1.Peek(15) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0a69);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s422(s10, gas - 1)
      else
        ExecuteFromCFGNode_s413(s10, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 143
    * Starting at 0xa2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7cf

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x7cf;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x94280d6200000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0a60);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xa60;
      assert s11.Peek(7) == 0x7cf;
      assert s11.Peek(12) == 0x44d;
      assert s11.Peek(18) == 0x173;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s13, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xa60

    requires s0.stack[7] == 0x7cf

    requires s0.stack[12] == 0x44d

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa60;
      assert s1.Peek(7) == 0x7cf;
      assert s1.Peek(12) == 0x44d;
      assert s1.Peek(18) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0xa60;
      assert s11.Peek(10) == 0x7cf;
      assert s11.Peek(15) == 0x44d;
      assert s11.Peek(21) == 0x173;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s14, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0xa60

    requires s0.stack[11] == 0x7cf

    requires s0.stack[16] == 0x44d

    requires s0.stack[22] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0xa60;
      assert s1.Peek(11) == 0x7cf;
      assert s1.Peek(16) == 0x44d;
      assert s1.Peek(22) == 0x173;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s5, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0xa60

    requires s0.stack[13] == 0x7cf

    requires s0.stack[18] == 0x44d

    requires s0.stack[24] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0xa60;
      assert s1.Peek(13) == 0x7cf;
      assert s1.Peek(18) == 0x44d;
      assert s1.Peek(24) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s6, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0xa60

    requires s0.stack[16] == 0x7cf

    requires s0.stack[21] == 0x44d

    requires s0.stack[27] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0xa60;
      assert s1.Peek(16) == 0x7cf;
      assert s1.Peek(21) == 0x44d;
      assert s1.Peek(27) == 0x173;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s418(s11, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0xa60

    requires s0.stack[15] == 0x7cf

    requires s0.stack[20] == 0x44d

    requires s0.stack[26] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0xa60;
      assert s1.Peek(15) == 0x7cf;
      assert s1.Peek(20) == 0x44d;
      assert s1.Peek(26) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s419(s7, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0xa60

    requires s0.stack[12] == 0x7cf

    requires s0.stack[17] == 0x44d

    requires s0.stack[23] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0xa60;
      assert s1.Peek(12) == 0x7cf;
      assert s1.Peek(17) == 0x44d;
      assert s1.Peek(23) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s6, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xa60

    requires s0.stack[8] == 0x7cf

    requires s0.stack[13] == 0x44d

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa60;
      assert s1.Peek(8) == 0x7cf;
      assert s1.Peek(13) == 0x44d;
      assert s1.Peek(19) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s6, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 144
    * Starting at 0xa60
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x7cf

    requires s0.stack[10] == 0x44d

    requires s0.stack[16] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7cf;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
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

  /** Node 422
    * Segment Id for this node is: 145
    * Starting at 0xa69
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7cf

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7cf;
      assert s1.Peek(9) == 0x44d;
      assert s1.Peek(15) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup7(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x7cf;
      assert s11.Peek(12) == 0x44d;
      assert s11.Peek(18) == 0x173;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x7cf;
      assert s21.Peek(12) == 0x44d;
      assert s21.Peek(18) == 0x173;
      var s22 := Dup6(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x7cf;
      assert s31.Peek(12) == 0x44d;
      assert s31.Peek(18) == 0x173;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s423(s41, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 146
    * Starting at 0xae7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7cf

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0x7cf;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0b52);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s431(s4, gas - 1)
      else
        ExecuteFromCFGNode_s424(s4, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 147
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7cf

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(5) == 0x7cf;
      assert s1.Peek(10) == 0x44d;
      assert s1.Peek(16) == 0x173;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup5(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x0b49);
      assert s11.Peek(0) == 0xb49;
      assert s11.Peek(10) == 0x7cf;
      assert s11.Peek(15) == 0x44d;
      assert s11.Peek(21) == 0x173;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x1063);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s425(s15, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 214
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xb49

    requires s0.stack[10] == 0x7cf

    requires s0.stack[15] == 0x44d

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb49;
      assert s1.Peek(10) == 0x7cf;
      assert s1.Peek(15) == 0x44d;
      assert s1.Peek(21) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1076);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1076;
      assert s11.Peek(5) == 0xb49;
      assert s11.Peek(13) == 0x7cf;
      assert s11.Peek(18) == 0x44d;
      assert s11.Peek(24) == 0x173;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x1054);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s426(s14, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0x1076

    requires s0.stack[6] == 0xb49

    requires s0.stack[14] == 0x7cf

    requires s0.stack[19] == 0x44d

    requires s0.stack[25] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1076;
      assert s1.Peek(6) == 0xb49;
      assert s1.Peek(14) == 0x7cf;
      assert s1.Peek(19) == 0x44d;
      assert s1.Peek(25) == 0x173;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s427(s5, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x1076

    requires s0.stack[8] == 0xb49

    requires s0.stack[16] == 0x7cf

    requires s0.stack[21] == 0x44d

    requires s0.stack[27] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x1076;
      assert s1.Peek(8) == 0xb49;
      assert s1.Peek(16) == 0x7cf;
      assert s1.Peek(21) == 0x44d;
      assert s1.Peek(27) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s428(s9, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x1076

    requires s0.stack[7] == 0xb49

    requires s0.stack[15] == 0x7cf

    requires s0.stack[20] == 0x44d

    requires s0.stack[26] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1076;
      assert s1.Peek(7) == 0xb49;
      assert s1.Peek(15) == 0x7cf;
      assert s1.Peek(20) == 0x44d;
      assert s1.Peek(26) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s429(s6, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 215
    * Starting at 0x1076
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1076 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0xb49

    requires s0.stack[11] == 0x7cf

    requires s0.stack[16] == 0x44d

    requires s0.stack[22] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb49;
      assert s1.Peek(11) == 0x7cf;
      assert s1.Peek(16) == 0x44d;
      assert s1.Peek(22) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s6, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 148
    * Starting at 0xb49
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x7cf

    requires s0.stack[13] == 0x44d

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x7cf;
      assert s1.Peek(13) == 0x44d;
      assert s1.Peek(19) == 0x173;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s431(s8, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 149
    * Starting at 0xb52
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x7cf

    requires s0.stack[9] == 0x44d

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7cf;
      assert s1.Peek(9) == 0x44d;
      assert s1.Peek(15) == 0x173;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s6, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 127
    * Starting at 0x7cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x44d

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s433(s1, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 128
    * Starting at 0x7d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x44d

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x44d;
      assert s1.Peek(10) == 0x173;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s6, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 83
    * Starting at 0x44d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x173;
      var s2 := Push2(s1, 0x0458);
      var s3 := Dup6(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x07d6);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s7, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 129
    * Starting at 0x7d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x458

    requires s0.stack[9] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x458;
      assert s1.Peek(9) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0846);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s445(s10, gas - 1)
      else
        ExecuteFromCFGNode_s436(s10, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 130
    * Starting at 0x80a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x458

    requires s0.stack[9] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x458;
      assert s1.Peek(10) == 0x173;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x96c6fd1e00000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x083d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x83d;
      assert s11.Peek(6) == 0x458;
      assert s11.Peek(12) == 0x173;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s437(s13, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x83d

    requires s0.stack[6] == 0x458

    requires s0.stack[12] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x83d;
      assert s1.Peek(6) == 0x458;
      assert s1.Peek(12) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x83d;
      assert s11.Peek(9) == 0x458;
      assert s11.Peek(15) == 0x173;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s438(s14, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x83d

    requires s0.stack[10] == 0x458

    requires s0.stack[16] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x83d;
      assert s1.Peek(10) == 0x458;
      assert s1.Peek(16) == 0x173;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s5, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x83d

    requires s0.stack[12] == 0x458

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x83d;
      assert s1.Peek(12) == 0x458;
      assert s1.Peek(18) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s440(s6, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x83d

    requires s0.stack[15] == 0x458

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x83d;
      assert s1.Peek(15) == 0x458;
      assert s1.Peek(21) == 0x173;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s441(s11, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x83d

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x83d;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s7, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x83d

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x83d;
      assert s1.Peek(11) == 0x458;
      assert s1.Peek(17) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s6, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x83d

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x83d;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s6, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 131
    * Starting at 0x83d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x458

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x458;
      assert s1.Peek(10) == 0x173;
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

  /** Node 445
    * Segment Id for this node is: 132
    * Starting at 0x846
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x846 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x458

    requires s0.stack[9] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x458;
      assert s1.Peek(9) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x08b6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s455(s10, gas - 1)
      else
        ExecuteFromCFGNode_s446(s10, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 133
    * Starting at 0x87a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x458

    requires s0.stack[9] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x458;
      assert s1.Peek(10) == 0x173;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xec442f0500000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x08ad);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x8ad;
      assert s11.Peek(6) == 0x458;
      assert s11.Peek(12) == 0x173;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s447(s13, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x8ad

    requires s0.stack[6] == 0x458

    requires s0.stack[12] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8ad;
      assert s1.Peek(6) == 0x458;
      assert s1.Peek(12) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x8ad;
      assert s11.Peek(9) == 0x458;
      assert s11.Peek(15) == 0x173;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s14, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x8ad

    requires s0.stack[10] == 0x458

    requires s0.stack[16] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x8ad;
      assert s1.Peek(10) == 0x458;
      assert s1.Peek(16) == 0x173;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s449(s5, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x8ad

    requires s0.stack[12] == 0x458

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x8ad;
      assert s1.Peek(12) == 0x458;
      assert s1.Peek(18) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s6, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x8ad

    requires s0.stack[15] == 0x458

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x8ad;
      assert s1.Peek(15) == 0x458;
      assert s1.Peek(21) == 0x173;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s451(s11, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x8ad

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x8ad;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s7, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x8ad

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x8ad;
      assert s1.Peek(11) == 0x458;
      assert s1.Peek(17) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s6, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8ad

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ad;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s6, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 134
    * Starting at 0x8ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x458

    requires s0.stack[10] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x458;
      assert s1.Peek(10) == 0x173;
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

  /** Node 455
    * Segment Id for this node is: 135
    * Starting at 0x8b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x458

    requires s0.stack[9] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x458;
      assert s1.Peek(9) == 0x173;
      var s2 := Push2(s1, 0x08c1);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b58);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s7, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 150
    * Starting at 0xb58
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0ba8);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s520(s10, gas - 1)
      else
        ExecuteFromCFGNode_s457(s10, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 151
    * Starting at 0xb8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x458;
      assert s1.Peek(14) == 0x173;
      var s2 := Push1(s1, 0x03);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := SLoad(s5);
      var s7 := Push2(s6, 0x0b9c);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1250);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s458(s11, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 255
    * Starting at 0x1250
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1250 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xb9c

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb9c;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x125a);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0fb0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s6, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x125a

    requires s0.stack[5] == 0xb9c

    requires s0.stack[12] == 0x8c1

    requires s0.stack[16] == 0x458

    requires s0.stack[22] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x125a;
      assert s1.Peek(5) == 0xb9c;
      assert s1.Peek(12) == 0x8c1;
      assert s1.Peek(16) == 0x458;
      assert s1.Peek(22) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s9, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 256
    * Starting at 0x125a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0xb9c

    requires s0.stack[11] == 0x8c1

    requires s0.stack[15] == 0x458

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb9c;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x458;
      assert s1.Peek(21) == 0x173;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1265);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0fb0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s7, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x1265

    requires s0.stack[5] == 0xb9c

    requires s0.stack[12] == 0x8c1

    requires s0.stack[16] == 0x458

    requires s0.stack[22] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1265;
      assert s1.Peek(5) == 0xb9c;
      assert s1.Peek(12) == 0x8c1;
      assert s1.Peek(16) == 0x458;
      assert s1.Peek(22) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s9, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 257
    * Starting at 0x1265
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0xb9c

    requires s0.stack[11] == 0x8c1

    requires s0.stack[15] == 0x458

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb9c;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x458;
      assert s1.Peek(21) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xb9c;
      assert s11.Peek(11) == 0x8c1;
      assert s11.Peek(15) == 0x458;
      assert s11.Peek(21) == 0x173;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x127d);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s465(s14, gas - 1)
      else
        ExecuteFromCFGNode_s463(s14, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 258
    * Starting at 0x1275
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1275 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xb9c

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x127c);
      assert s1.Peek(0) == 0x127c;
      assert s1.Peek(4) == 0xb9c;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x458;
      assert s1.Peek(21) == 0x173;
      var s2 := Push2(s1, 0x1223);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s3, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 254
    * Starting at 0x1223
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1223 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x127c

    requires s0.stack[4] == 0xb9c

    requires s0.stack[11] == 0x8c1

    requires s0.stack[15] == 0x458

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x127c;
      assert s1.Peek(4) == 0xb9c;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x458;
      assert s1.Peek(21) == 0x173;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 465
    * Segment Id for this node is: 260
    * Starting at 0x127d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xb9c

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb9c;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s466(s6, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 152
    * Starting at 0xb9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x458;
      assert s1.Peek(17) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Push2(s8, 0x0c76);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s467(s10, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 157
    * Starting at 0xc76
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0cbd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s487(s10, gas - 1)
      else
        ExecuteFromCFGNode_s468(s10, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 158
    * Starting at 0xcaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x458;
      assert s1.Peek(14) == 0x173;
      var s2 := Push1(s1, 0x03);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := SLoad(s5);
      var s7 := Sub(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x458;
      assert s11.Peek(16) == 0x173;
      var s12 := Swap1(s11);
      var s13 := SStore(s12);
      var s14 := Pop(s13);
      var s15 := Push2(s14, 0x0db4);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s16, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 166
    * Starting at 0xdb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Push1(s1, 0xe4);
      var s3 := Push1(s2, 0x02);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x458;
      assert s11.Peek(16) == 0x173;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x8c1;
      assert s21.Peek(9) == 0x458;
      assert s21.Peek(15) == 0x173;
      var s22 := Sub(s21);
      var s23 := Push2(s22, 0x0e3e);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s471(s24, gas - 1)
      else
        ExecuteFromCFGNode_s470(s24, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 167
    * Starting at 0xdfa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f20);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x458;
      assert s1.Peek(14) == 0x173;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Dup5(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(7) == 0x8c1;
      assert s11.Peek(11) == 0x458;
      assert s11.Peek(17) == 0x173;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(6) == 0x8c1;
      assert s21.Peek(10) == 0x458;
      assert s21.Peek(16) == 0x173;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s471(s23, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 168
    * Starting at 0xe3e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push32(s7, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x8c1;
      assert s11.Peek(12) == 0x458;
      assert s11.Peek(18) == 0x173;
      var s12 := Push2(s11, 0x0e9b);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x1063);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s16, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 214
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xe9b

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe9b;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1076);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1076;
      assert s11.Peek(5) == 0xe9b;
      assert s11.Peek(12) == 0x8c1;
      assert s11.Peek(16) == 0x458;
      assert s11.Peek(22) == 0x173;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x1054);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s14, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x1076

    requires s0.stack[6] == 0xe9b

    requires s0.stack[13] == 0x8c1

    requires s0.stack[17] == 0x458

    requires s0.stack[23] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1076;
      assert s1.Peek(6) == 0xe9b;
      assert s1.Peek(13) == 0x8c1;
      assert s1.Peek(17) == 0x458;
      assert s1.Peek(23) == 0x173;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s474(s5, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x1076

    requires s0.stack[8] == 0xe9b

    requires s0.stack[15] == 0x8c1

    requires s0.stack[19] == 0x458

    requires s0.stack[25] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x1076;
      assert s1.Peek(8) == 0xe9b;
      assert s1.Peek(15) == 0x8c1;
      assert s1.Peek(19) == 0x458;
      assert s1.Peek(25) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s475(s9, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x1076

    requires s0.stack[7] == 0xe9b

    requires s0.stack[14] == 0x8c1

    requires s0.stack[18] == 0x458

    requires s0.stack[24] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1076;
      assert s1.Peek(7) == 0xe9b;
      assert s1.Peek(14) == 0x8c1;
      assert s1.Peek(18) == 0x458;
      assert s1.Peek(24) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s6, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 215
    * Starting at 0x1076
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1076 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xe9b

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe9b;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s477(s6, gas - 1)
  }

  /** Node 477
    * Segment Id for this node is: 169
    * Starting at 0xe9b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x458;
      assert s1.Peek(17) == 0x173;
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
      assert s11.Peek(0) == 0x8c1;
      assert s11.Peek(4) == 0x458;
      assert s11.Peek(10) == 0x173;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s478(s12, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 136
    * Starting at 0x8c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x458

    requires s0.stack[9] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x458;
      assert s1.Peek(9) == 0x173;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s479(s5, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 84
    * Starting at 0x458
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x458 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x173;
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
      ExecuteFromCFGNode_s480(s11, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 36
    * Starting at 0x173
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x173 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0180);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x103b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s481(s8, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 210
    * Starting at 0x103b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x180;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x104e);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x104e;
      assert s11.Peek(5) == 0x180;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x102c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s14, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 208
    * Starting at 0x102c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x104e

    requires s0.stack[6] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x104e;
      assert s1.Peek(6) == 0x180;
      var s2 := Push2(s1, 0x1035);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1021);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s5, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 207
    * Starting at 0x1021
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1021 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1035

    requires s0.stack[4] == 0x104e

    requires s0.stack[8] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1035;
      assert s1.Peek(4) == 0x104e;
      assert s1.Peek(8) == 0x180;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s484(s11, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 209
    * Starting at 0x1035
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x104e

    requires s0.stack[7] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x104e;
      assert s1.Peek(7) == 0x180;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s6, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 211
    * Starting at 0x104e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x180

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x180;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s486(s6, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 37
    * Starting at 0x180
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
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
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 487
    * Segment Id for this node is: 159
    * Starting at 0xcbd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Push2(s1, 0x0f20);
      var s3 := Push1(s2, 0x02);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x458;
      assert s11.Peek(16) == 0x173;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x8c1;
      assert s21.Peek(9) == 0x458;
      assert s21.Peek(15) == 0x173;
      var s22 := Push1(s21, 0x02);
      var s23 := Push0(s22);
      var s24 := Dup7(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Push20(s26, 0xffffffffffffffffffffffffffffffffffffffff);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(8) == 0x8c1;
      assert s31.Peek(12) == 0x458;
      assert s31.Peek(18) == 0x173;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Dup2(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x20);
      var s37 := Add(s36);
      var s38 := Push0(s37);
      var s39 := Keccak256(s38);
      var s40 := SLoad(s39);
      var s41 := Push2(s40, 0x0d46);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s488(s41, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 160
    * Starting at 0xd40
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xd46

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x458;
      assert s1.Peek(17) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Push2(s2, 0x1250);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s4, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 255
    * Starting at 0x1250
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1250 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xd46

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x458;
      assert s1.Peek(17) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x125a);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0fb0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s6, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x125a

    requires s0.stack[5] == 0xd46

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x125a;
      assert s1.Peek(5) == 0xd46;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s9, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 256
    * Starting at 0x125a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd46

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1265);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0fb0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s7, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x1265

    requires s0.stack[5] == 0xd46

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1265;
      assert s1.Peek(5) == 0xd46;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s493(s9, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 257
    * Starting at 0x1265
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd46

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xd46;
      assert s11.Peek(9) == 0x8c1;
      assert s11.Peek(13) == 0x458;
      assert s11.Peek(19) == 0x173;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x127d);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s496(s14, gas - 1)
      else
        ExecuteFromCFGNode_s494(s14, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 258
    * Starting at 0x1275
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1275 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd46

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x458

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x127c);
      assert s1.Peek(0) == 0x127c;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Push2(s1, 0x1223);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s3, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 254
    * Starting at 0x1223
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1223 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x127c

    requires s0.stack[4] == 0xd46

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x127c;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 496
    * Segment Id for this node is: 260
    * Starting at 0x127d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd46

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x458

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x458;
      assert s1.Peek(18) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s497(s6, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 161
    * Starting at 0xd46
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x8c1

    requires s0.stack[9] == 0x458

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x8c1;
      assert s1.Peek(9) == 0x458;
      assert s1.Peek(15) == 0x173;
      var s2 := Lt(s1);
      var s3 := Push2(s2, 0x0d6a);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s519(s4, gas - 1)
      else
        ExecuteFromCFGNode_s498(s4, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 162
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push3(s0, 0x0bd223);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x458;
      assert s1.Peek(14) == 0x173;
      var s2 := Push2(s1, 0x09e3);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0d5d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1283);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s8, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 261
    * Starting at 0x1283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xd5d

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5d;
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x458;
      assert s1.Peek(17) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x128d);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0fb0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s6, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x128d

    requires s0.stack[5] == 0xd5d

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128d;
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s9, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 262
    * Starting at 0x128d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd5d

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd5d;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1298);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0fb0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s7, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x1298

    requires s0.stack[5] == 0xd5d

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1298;
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s503(s9, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 263
    * Starting at 0x1298
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1298 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd5d

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd5d;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Mul(s5);
      var s7 := Push2(s6, 0x12a6);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fb0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s504(s10, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x12a6

    requires s0.stack[6] == 0xd5d

    requires s0.stack[11] == 0x8c1

    requires s0.stack[15] == 0x458

    requires s0.stack[21] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12a6;
      assert s1.Peek(6) == 0xd5d;
      assert s1.Peek(11) == 0x8c1;
      assert s1.Peek(15) == 0x458;
      assert s1.Peek(21) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s505(s9, gas - 1)
  }

  /** Node 505
    * Segment Id for this node is: 264
    * Starting at 0x12a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xd5d

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Div(s5);
      var s7 := Dup5(s6);
      var s8 := Eq(s7);
      var s9 := Dup4(s8);
      var s10 := IsZero(s9);
      var s11 := Or(s10);
      assert s11.Peek(5) == 0xd5d;
      assert s11.Peek(10) == 0x8c1;
      assert s11.Peek(14) == 0x458;
      assert s11.Peek(20) == 0x173;
      var s12 := Push2(s11, 0x12bd);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s508(s13, gas - 1)
      else
        ExecuteFromCFGNode_s506(s13, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 265
    * Starting at 0x12b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd5d

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x12bc);
      assert s1.Peek(0) == 0x12bc;
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Push2(s1, 0x1223);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s507(s3, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 254
    * Starting at 0x1223
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1223 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x12bc

    requires s0.stack[5] == 0xd5d

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12bc;
      assert s1.Peek(5) == 0xd5d;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 508
    * Segment Id for this node is: 267
    * Starting at 0x12bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd5d

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd5d;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s509(s7, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 163
    * Starting at 0xd5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x8c1

    requires s0.stack[9] == 0x458

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x8c1;
      assert s1.Peek(9) == 0x458;
      assert s1.Peek(15) == 0x173;
      var s2 := Push2(s1, 0x0d67);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x12f1);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s6, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 269
    * Starting at 0x12f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xd67

    requires s0.stack[6] == 0x8c1

    requires s0.stack[10] == 0x458

    requires s0.stack[16] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd67;
      assert s1.Peek(6) == 0x8c1;
      assert s1.Peek(10) == 0x458;
      assert s1.Peek(16) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x12fb);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0fb0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s511(s6, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x12fb

    requires s0.stack[5] == 0xd67

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12fb;
      assert s1.Peek(5) == 0xd67;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s9, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 270
    * Starting at 0x12fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd67

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x458

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd67;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x458;
      assert s1.Peek(18) == 0x173;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1306);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0fb0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s7, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1306

    requires s0.stack[5] == 0xd67

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1306;
      assert s1.Peek(5) == 0xd67;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s514(s9, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 271
    * Starting at 0x1306
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1306 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd67

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x458

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd67;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x458;
      assert s1.Peek(18) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1316);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s517(s6, gas - 1)
      else
        ExecuteFromCFGNode_s515(s6, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 272
    * Starting at 0x130e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x130e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd67

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1315);
      assert s1.Peek(0) == 0x1315;
      assert s1.Peek(4) == 0xd67;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x458;
      assert s1.Peek(18) == 0x173;
      var s2 := Push2(s1, 0x12c4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s516(s3, gas - 1)
  }

  /** Node 516
    * Segment Id for this node is: 268
    * Starting at 0x12c4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x1315

    requires s0.stack[4] == 0xd67

    requires s0.stack[8] == 0x8c1

    requires s0.stack[12] == 0x458

    requires s0.stack[18] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1315;
      assert s1.Peek(4) == 0xd67;
      assert s1.Peek(8) == 0x8c1;
      assert s1.Peek(12) == 0x458;
      assert s1.Peek(18) == 0x173;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x12);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 517
    * Segment Id for this node is: 274
    * Starting at 0x1316
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1316 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd67

    requires s0.stack[7] == 0x8c1

    requires s0.stack[11] == 0x458

    requires s0.stack[17] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd67;
      assert s1.Peek(7) == 0x8c1;
      assert s1.Peek(11) == 0x458;
      assert s1.Peek(17) == 0x173;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Div(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s518(s11, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 164
    * Starting at 0xd67
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x8c1

    requires s0.stack[8] == 0x458

    requires s0.stack[14] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x458;
      assert s1.Peek(14) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s519(s3, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 165
    * Starting at 0xd6a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Dup1(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x458;
      assert s11.Peek(16) == 0x173;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(6) == 0x8c1;
      assert s21.Peek(10) == 0x458;
      assert s21.Peek(16) == 0x173;
      var s22 := Dup3(s21);
      var s23 := Dup3(s22);
      var s24 := SLoad(s23);
      var s25 := Add(s24);
      var s26 := Swap3(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := SStore(s30);
      assert s31.Peek(4) == 0x8c1;
      assert s31.Peek(8) == 0x458;
      assert s31.Peek(14) == 0x173;
      var s32 := Pop(s31);
      // Segment is terminal (Revert, Stop or Return)
      s32
  }

  /** Node 520
    * Segment Id for this node is: 153
    * Starting at 0xba8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x8c1

    requires s0.stack[7] == 0x458

    requires s0.stack[13] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8c1;
      assert s1.Peek(7) == 0x458;
      assert s1.Peek(13) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x8c1;
      assert s11.Peek(10) == 0x458;
      assert s11.Peek(16) == 0x173;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x8c1;
      assert s21.Peek(9) == 0x458;
      assert s21.Peek(15) == 0x173;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0c31);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s538(s29, gas - 1)
      else
        ExecuteFromCFGNode_s521(s29, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 154
    * Starting at 0xbf1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x8c1

    requires s0.stack[8] == 0x458

    requires s0.stack[14] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(5) == 0x8c1;
      assert s1.Peek(9) == 0x458;
      assert s1.Peek(15) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xe450d38c00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c28);
      assert s11.Peek(0) == 0xc28;
      assert s11.Peek(9) == 0x8c1;
      assert s11.Peek(13) == 0x458;
      assert s11.Peek(19) == 0x173;
      var s12 := Swap4(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x11ee);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s522(s17, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 250
    * Starting at 0x11ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xc28

    requires s0.stack[9] == 0x8c1

    requires s0.stack[13] == 0x458

    requires s0.stack[19] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc28;
      assert s1.Peek(9) == 0x8c1;
      assert s1.Peek(13) == 0x458;
      assert s1.Peek(19) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1201);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1201;
      assert s11.Peek(7) == 0xc28;
      assert s11.Peek(12) == 0x8c1;
      assert s11.Peek(16) == 0x458;
      assert s11.Peek(22) == 0x173;
      var s12 := Dup7(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s523(s14, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x1201

    requires s0.stack[8] == 0xc28

    requires s0.stack[13] == 0x8c1

    requires s0.stack[17] == 0x458

    requires s0.stack[23] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1201;
      assert s1.Peek(8) == 0xc28;
      assert s1.Peek(13) == 0x8c1;
      assert s1.Peek(17) == 0x458;
      assert s1.Peek(23) == 0x173;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s524(s5, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x1201

    requires s0.stack[10] == 0xc28

    requires s0.stack[15] == 0x8c1

    requires s0.stack[19] == 0x458

    requires s0.stack[25] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x1201;
      assert s1.Peek(10) == 0xc28;
      assert s1.Peek(15) == 0x8c1;
      assert s1.Peek(19) == 0x458;
      assert s1.Peek(25) == 0x173;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s525(s6, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x1201

    requires s0.stack[13] == 0xc28

    requires s0.stack[18] == 0x8c1

    requires s0.stack[22] == 0x458

    requires s0.stack[28] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x1201;
      assert s1.Peek(13) == 0xc28;
      assert s1.Peek(18) == 0x8c1;
      assert s1.Peek(22) == 0x458;
      assert s1.Peek(28) == 0x173;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s526(s11, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x1201

    requires s0.stack[12] == 0xc28

    requires s0.stack[17] == 0x8c1

    requires s0.stack[21] == 0x458

    requires s0.stack[27] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x1201;
      assert s1.Peek(12) == 0xc28;
      assert s1.Peek(17) == 0x8c1;
      assert s1.Peek(21) == 0x458;
      assert s1.Peek(27) == 0x173;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s7, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x1201

    requires s0.stack[9] == 0xc28

    requires s0.stack[14] == 0x8c1

    requires s0.stack[18] == 0x458

    requires s0.stack[24] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1201;
      assert s1.Peek(9) == 0xc28;
      assert s1.Peek(14) == 0x8c1;
      assert s1.Peek(18) == 0x458;
      assert s1.Peek(24) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s528(s6, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 251
    * Starting at 0x1201
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1201 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xc28

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc28;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Push2(s1, 0x120e);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x1054);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s529(s8, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x120e

    requires s0.stack[8] == 0xc28

    requires s0.stack[13] == 0x8c1

    requires s0.stack[17] == 0x458

    requires s0.stack[23] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x120e;
      assert s1.Peek(8) == 0xc28;
      assert s1.Peek(13) == 0x8c1;
      assert s1.Peek(17) == 0x458;
      assert s1.Peek(23) == 0x173;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s530(s5, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x120e

    requires s0.stack[10] == 0xc28

    requires s0.stack[15] == 0x8c1

    requires s0.stack[19] == 0x458

    requires s0.stack[25] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x120e;
      assert s1.Peek(10) == 0xc28;
      assert s1.Peek(15) == 0x8c1;
      assert s1.Peek(19) == 0x458;
      assert s1.Peek(25) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s531(s9, gas - 1)
  }

  /** Node 531
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x120e

    requires s0.stack[9] == 0xc28

    requires s0.stack[14] == 0x8c1

    requires s0.stack[18] == 0x458

    requires s0.stack[24] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x120e;
      assert s1.Peek(9) == 0xc28;
      assert s1.Peek(14) == 0x8c1;
      assert s1.Peek(18) == 0x458;
      assert s1.Peek(24) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s532(s6, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 252
    * Starting at 0x120e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xc28

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc28;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Push2(s1, 0x121b);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x1054);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s533(s8, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x121b

    requires s0.stack[8] == 0xc28

    requires s0.stack[13] == 0x8c1

    requires s0.stack[17] == 0x458

    requires s0.stack[23] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x121b;
      assert s1.Peek(8) == 0xc28;
      assert s1.Peek(13) == 0x8c1;
      assert s1.Peek(17) == 0x458;
      assert s1.Peek(23) == 0x173;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s534(s5, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x121b

    requires s0.stack[10] == 0xc28

    requires s0.stack[15] == 0x8c1

    requires s0.stack[19] == 0x458

    requires s0.stack[25] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x121b;
      assert s1.Peek(10) == 0xc28;
      assert s1.Peek(15) == 0x8c1;
      assert s1.Peek(19) == 0x458;
      assert s1.Peek(25) == 0x173;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s535(s9, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x121b

    requires s0.stack[9] == 0xc28

    requires s0.stack[14] == 0x8c1

    requires s0.stack[18] == 0x458

    requires s0.stack[24] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x121b;
      assert s1.Peek(9) == 0xc28;
      assert s1.Peek(14) == 0x8c1;
      assert s1.Peek(18) == 0x458;
      assert s1.Peek(24) == 0x173;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s6, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 253
    * Starting at 0x121b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xc28

    requires s0.stack[10] == 0x8c1

    requires s0.stack[14] == 0x458

    requires s0.stack[20] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc28;
      assert s1.Peek(10) == 0x8c1;
      assert s1.Peek(14) == 0x458;
      assert s1.Peek(20) == 0x173;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s537(s8, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 155
    * Starting at 0xc28
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x8c1

    requires s0.stack[9] == 0x458

    requires s0.stack[15] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x8c1;
      assert s1.Peek(9) == 0x458;
      assert s1.Peek(15) == 0x173;
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

  /** Node 538
    * Segment Id for this node is: 156
    * Starting at 0xc31
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x8c1

    requires s0.stack[8] == 0x458

    requires s0.stack[14] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x8c1;
      assert s1.Peek(8) == 0x458;
      assert s1.Peek(14) == 0x173;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push0(s4);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x8c1;
      assert s11.Peek(12) == 0x458;
      assert s11.Peek(18) == 0x173;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x8c1;
      assert s21.Peek(11) == 0x458;
      assert s21.Peek(17) == 0x173;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s467(s27, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 31
    * Starting at 0x13d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0157);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0152);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(3) == 0x157;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x107c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s14, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 216
    * Starting at 0x107c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x152

    requires s0.stack[3] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x152;
      assert s1.Peek(3) == 0x157;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1091);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s543(s10, gas - 1)
      else
        ExecuteFromCFGNode_s541(s10, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 217
    * Starting at 0x1089
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1089 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x152

    requires s0.stack[4] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1090);
      assert s1.Peek(0) == 0x1090;
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(5) == 0x157;
      var s2 := Push2(s1, 0x0f52);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s3, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 184
    * Starting at 0xf52
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x1090

    requires s0.stack[4] == 0x152

    requires s0.stack[5] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1090;
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(5) == 0x157;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 543
    * Segment Id for this node is: 219
    * Starting at 0x1091
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1091 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x152

    requires s0.stack[4] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x152;
      assert s1.Peek(4) == 0x157;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x109e);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0f9c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s544(s9, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x109e

    requires s0.stack[7] == 0x152

    requires s0.stack[8] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109e;
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(8) == 0x157;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s545(s10, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x152

    requires s0.stack[11] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x109e;
      assert s1.Peek(10) == 0x152;
      assert s1.Peek(11) == 0x157;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s546(s5, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x109e

    requires s0.stack[12] == 0x152

    requires s0.stack[13] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x109e;
      assert s1.Peek(12) == 0x152;
      assert s1.Peek(13) == 0x157;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s6, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x109e

    requires s0.stack[15] == 0x152

    requires s0.stack[16] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x109e;
      assert s1.Peek(15) == 0x152;
      assert s1.Peek(16) == 0x157;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s548(s11, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x109e

    requires s0.stack[14] == 0x152

    requires s0.stack[15] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x109e;
      assert s1.Peek(14) == 0x152;
      assert s1.Peek(15) == 0x157;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s549(s7, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x109e

    requires s0.stack[11] == 0x152

    requires s0.stack[12] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x109e;
      assert s1.Peek(11) == 0x152;
      assert s1.Peek(12) == 0x157;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s551(s5, gas - 1)
      else
        ExecuteFromCFGNode_s550(s5, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x152

    requires s0.stack[11] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x109e;
      assert s1.Peek(11) == 0x152;
      assert s1.Peek(12) == 0x157;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 551
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x109e

    requires s0.stack[10] == 0x152

    requires s0.stack[11] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x109e;
      assert s1.Peek(10) == 0x152;
      assert s1.Peek(11) == 0x157;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s552(s3, gas - 1)
  }

  /** Node 552
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x109e

    requires s0.stack[8] == 0x152

    requires s0.stack[9] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x109e;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(9) == 0x157;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s553(s6, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 220
    * Starting at 0x109e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x152

    requires s0.stack[6] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(6) == 0x157;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s9, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 32
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x157;
      var s2 := Push2(s1, 0x03eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s555(s3, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 79
    * Starting at 0x3eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x157;
      var s2 := Push2(s1, 0x03f3);
      var s3 := Push2(s2, 0x06bd);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s556(s4, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 114
    * Starting at 0x6bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x3f3

    requires s0.stack[2] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3f3;
      assert s1.Peek(2) == 0x157;
      var s2 := Push2(s1, 0x06c5);
      var s3 := Push2(s2, 0x06a4);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s557(s4, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x6c5

    requires s0.stack[1] == 0x3f3

    requires s0.stack[3] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6c5;
      assert s1.Peek(1) == 0x3f3;
      assert s1.Peek(3) == 0x157;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s558(s7, gas - 1)
  }

  /** Node 558
    * Segment Id for this node is: 115
    * Starting at 0x6c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x3f3

    requires s0.stack[3] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3f3;
      assert s1.Peek(3) == 0x157;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x06e3);
      var s5 := Push2(s4, 0x04c4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s559(s6, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 90
    * Starting at 0x4c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x6e3

    requires s0.stack[2] == 0x3f3

    requires s0.stack[4] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6e3;
      assert s1.Peek(2) == 0x3f3;
      assert s1.Peek(4) == 0x157;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x07);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x6e3;
      assert s11.Peek(4) == 0x3f3;
      assert s11.Peek(6) == 0x157;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s560(s17, gas - 1)
  }

  /** Node 560
    * Segment Id for this node is: 116
    * Starting at 0x6e3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x3f3

    requires s0.stack[4] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f3;
      assert s1.Peek(4) == 0x157;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0742);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s572(s6, gas - 1)
      else
        ExecuteFromCFGNode_s561(s6, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 117
    * Starting at 0x6ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x3f3

    requires s0.stack[2] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0706);
      assert s1.Peek(0) == 0x706;
      assert s1.Peek(1) == 0x3f3;
      assert s1.Peek(3) == 0x157;
      var s2 := Push2(s1, 0x06a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s562(s3, gas - 1)
  }

  /** Node 562
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x706

    requires s0.stack[1] == 0x3f3

    requires s0.stack[3] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x706;
      assert s1.Peek(1) == 0x3f3;
      assert s1.Peek(3) == 0x157;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s563(s7, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 118
    * Starting at 0x706
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x706 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x3f3

    requires s0.stack[3] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3f3;
      assert s1.Peek(3) == 0x157;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0739);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x739;
      assert s11.Peek(3) == 0x3f3;
      assert s11.Peek(5) == 0x157;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s13, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x739

    requires s0.stack[3] == 0x3f3

    requires s0.stack[5] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x739;
      assert s1.Peek(3) == 0x3f3;
      assert s1.Peek(5) == 0x157;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x739;
      assert s11.Peek(6) == 0x3f3;
      assert s11.Peek(8) == 0x157;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s565(s14, gas - 1)
  }

  /** Node 565
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x739

    requires s0.stack[7] == 0x3f3

    requires s0.stack[9] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x739;
      assert s1.Peek(7) == 0x3f3;
      assert s1.Peek(9) == 0x157;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s566(s5, gas - 1)
  }

  /** Node 566
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x739

    requires s0.stack[9] == 0x3f3

    requires s0.stack[11] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x739;
      assert s1.Peek(9) == 0x3f3;
      assert s1.Peek(11) == 0x157;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s567(s6, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x739

    requires s0.stack[12] == 0x3f3

    requires s0.stack[14] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x739;
      assert s1.Peek(12) == 0x3f3;
      assert s1.Peek(14) == 0x157;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s568(s11, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x739

    requires s0.stack[11] == 0x3f3

    requires s0.stack[13] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x739;
      assert s1.Peek(11) == 0x3f3;
      assert s1.Peek(13) == 0x157;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s7, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x739

    requires s0.stack[8] == 0x3f3

    requires s0.stack[10] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x739;
      assert s1.Peek(8) == 0x3f3;
      assert s1.Peek(10) == 0x157;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s570(s6, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x739

    requires s0.stack[4] == 0x3f3

    requires s0.stack[6] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x739;
      assert s1.Peek(4) == 0x3f3;
      assert s1.Peek(6) == 0x157;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s571(s6, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 119
    * Starting at 0x739
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x3f3

    requires s0.stack[3] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3f3;
      assert s1.Peek(3) == 0x157;
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

  /** Node 572
    * Segment Id for this node is: 120
    * Starting at 0x742
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x742 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x3f3

    requires s0.stack[2] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3f3;
      assert s1.Peek(2) == 0x157;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s573(s2, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 80
    * Starting at 0x3f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x157

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x157;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x06);
      var s4 := Push0(s3);
      var s5 := Push2(s4, 0x0100);
      var s6 := Exp(s5);
      var s7 := Dup2(s6);
      var s8 := SLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := Mul(s10);
      assert s11.Peek(6) == 0x157;
      var s12 := Not(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Dup4(s14);
      var s16 := Push20(s15, 0xffffffffffffffffffffffffffffffffffffffff);
      var s17 := And(s16);
      var s18 := Mul(s17);
      var s19 := Or(s18);
      var s20 := Swap1(s19);
      var s21 := SStore(s20);
      assert s21.Peek(2) == 0x157;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s574(s24, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 33
    * Starting at 0x157
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157 as nat
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

  /** Node 575
    * Segment Id for this node is: 28
    * Starting at 0x11f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0127);
      var s3 := Push2(s2, 0x03e2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s576(s4, gas - 1)
  }

  /** Node 576
    * Segment Id for this node is: 78
    * Starting at 0x3e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x127;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s577(s8, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 29
    * Starting at 0x127
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0134);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1063);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s578(s8, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 214
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x134;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1076);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1076;
      assert s11.Peek(5) == 0x134;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x1054);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s579(s14, gas - 1)
  }

  /** Node 579
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1076

    requires s0.stack[6] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1076;
      assert s1.Peek(6) == 0x134;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s580(s5, gas - 1)
  }

  /** Node 580
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x1076

    requires s0.stack[8] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x1076;
      assert s1.Peek(8) == 0x134;
      var s2 := Push0(s1);
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
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1076

    requires s0.stack[7] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1076;
      assert s1.Peek(7) == 0x134;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s582(s6, gas - 1)
  }

  /** Node 582
    * Segment Id for this node is: 215
    * Starting at 0x1076
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1076 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x134;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s583(s6, gas - 1)
  }

  /** Node 583
    * Segment Id for this node is: 30
    * Starting at 0x134
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s583(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x134 as nat
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

  /** Node 584
    * Segment Id for this node is: 24
    * Starting at 0xef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s584(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0109);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0104);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x104;
      assert s11.Peek(3) == 0x109;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0fe3);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s585(s14, gas - 1)
  }

  /** Node 585
    * Segment Id for this node is: 201
    * Starting at 0xfe3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s585(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x104

    requires s0.stack[3] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x104;
      assert s1.Peek(3) == 0x109;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0ff9);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s588(s11, gas - 1)
      else
        ExecuteFromCFGNode_s586(s11, gas - 1)
  }

  /** Node 586
    * Segment Id for this node is: 202
    * Starting at 0xff1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s586(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x104

    requires s0.stack[5] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ff8);
      assert s1.Peek(0) == 0xff8;
      assert s1.Peek(5) == 0x104;
      assert s1.Peek(6) == 0x109;
      var s2 := Push2(s1, 0x0f52);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s587(s3, gas - 1)
  }

  /** Node 587
    * Segment Id for this node is: 184
    * Starting at 0xf52
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s587(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xff8

    requires s0.stack[5] == 0x104

    requires s0.stack[6] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xff8;
      assert s1.Peek(5) == 0x104;
      assert s1.Peek(6) == 0x109;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 588
    * Segment Id for this node is: 204
    * Starting at 0xff9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s588(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x104

    requires s0.stack[5] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x104;
      assert s1.Peek(5) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1006);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0f9c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s589(s9, gas - 1)
  }

  /** Node 589
    * Segment Id for this node is: 192
    * Starting at 0xf9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s589(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1006

    requires s0.stack[8] == 0x104

    requires s0.stack[9] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1006;
      assert s1.Peek(8) == 0x104;
      assert s1.Peek(9) == 0x109;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0faa);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0f86);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s590(s10, gas - 1)
  }

  /** Node 590
    * Segment Id for this node is: 188
    * Starting at 0xf86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s590(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1006

    requires s0.stack[11] == 0x104

    requires s0.stack[12] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x1006;
      assert s1.Peek(11) == 0x104;
      assert s1.Peek(12) == 0x109;
      var s2 := Push2(s1, 0x0f8f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s591(s5, gas - 1)
  }

  /** Node 591
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s591(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xf8f

    requires s0.stack[3] == 0xfaa

    requires s0.stack[7] == 0x1006

    requires s0.stack[13] == 0x104

    requires s0.stack[14] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf8f;
      assert s1.Peek(3) == 0xfaa;
      assert s1.Peek(7) == 0x1006;
      assert s1.Peek(13) == 0x104;
      assert s1.Peek(14) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s592(s6, gas - 1)
  }

  /** Node 592
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s592(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0xf8f

    requires s0.stack[6] == 0xfaa

    requires s0.stack[10] == 0x1006

    requires s0.stack[16] == 0x104

    requires s0.stack[17] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0xf8f;
      assert s1.Peek(6) == 0xfaa;
      assert s1.Peek(10) == 0x1006;
      assert s1.Peek(16) == 0x104;
      assert s1.Peek(17) == 0x109;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s593(s11, gas - 1)
  }

  /** Node 593
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s593(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xf8f

    requires s0.stack[5] == 0xfaa

    requires s0.stack[9] == 0x1006

    requires s0.stack[15] == 0x104

    requires s0.stack[16] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8f;
      assert s1.Peek(5) == 0xfaa;
      assert s1.Peek(9) == 0x1006;
      assert s1.Peek(15) == 0x104;
      assert s1.Peek(16) == 0x109;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s594(s7, gas - 1)
  }

  /** Node 594
    * Segment Id for this node is: 189
    * Starting at 0xf8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s594(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xfaa

    requires s0.stack[6] == 0x1006

    requires s0.stack[12] == 0x104

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x1006;
      assert s1.Peek(12) == 0x104;
      assert s1.Peek(13) == 0x109;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0f99);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s596(s5, gas - 1)
      else
        ExecuteFromCFGNode_s595(s5, gas - 1)
  }

  /** Node 595
    * Segment Id for this node is: 190
    * Starting at 0xf96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s595(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1006

    requires s0.stack[11] == 0x104

    requires s0.stack[12] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfaa;
      assert s1.Peek(6) == 0x1006;
      assert s1.Peek(12) == 0x104;
      assert s1.Peek(13) == 0x109;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 596
    * Segment Id for this node is: 191
    * Starting at 0xf99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s596(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfaa

    requires s0.stack[5] == 0x1006

    requires s0.stack[11] == 0x104

    requires s0.stack[12] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfaa;
      assert s1.Peek(5) == 0x1006;
      assert s1.Peek(11) == 0x104;
      assert s1.Peek(12) == 0x109;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s597(s3, gas - 1)
  }

  /** Node 597
    * Segment Id for this node is: 193
    * Starting at 0xfaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s597(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1006

    requires s0.stack[9] == 0x104

    requires s0.stack[10] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1006;
      assert s1.Peek(9) == 0x104;
      assert s1.Peek(10) == 0x109;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s598(s6, gas - 1)
  }

  /** Node 598
    * Segment Id for this node is: 205
    * Starting at 0x1006
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s598(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1006 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x104

    requires s0.stack[7] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x104;
      assert s1.Peek(7) == 0x109;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x1017);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0fcf);
      assert s11.Peek(0) == 0xfcf;
      assert s11.Peek(3) == 0x1017;
      assert s11.Peek(9) == 0x104;
      assert s11.Peek(10) == 0x109;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s599(s12, gas - 1)
  }

  /** Node 599
    * Segment Id for this node is: 199
    * Starting at 0xfcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s599(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1017

    requires s0.stack[8] == 0x104

    requires s0.stack[9] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1017;
      assert s1.Peek(8) == 0x104;
      assert s1.Peek(9) == 0x109;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0fdd);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fb9);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s600(s10, gas - 1)
  }

  /** Node 600
    * Segment Id for this node is: 195
    * Starting at 0xfb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s600(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x1017

    requires s0.stack[11] == 0x104

    requires s0.stack[12] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfdd;
      assert s1.Peek(5) == 0x1017;
      assert s1.Peek(11) == 0x104;
      assert s1.Peek(12) == 0x109;
      var s2 := Push2(s1, 0x0fc2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s601(s5, gas - 1)
  }

  /** Node 601
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s601(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xfc2

    requires s0.stack[3] == 0xfdd

    requires s0.stack[7] == 0x1017

    requires s0.stack[13] == 0x104

    requires s0.stack[14] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfc2;
      assert s1.Peek(3) == 0xfdd;
      assert s1.Peek(7) == 0x1017;
      assert s1.Peek(13) == 0x104;
      assert s1.Peek(14) == 0x109;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s602(s9, gas - 1)
  }

  /** Node 602
    * Segment Id for this node is: 196
    * Starting at 0xfc2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s602(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xfdd

    requires s0.stack[6] == 0x1017

    requires s0.stack[12] == 0x104

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfdd;
      assert s1.Peek(6) == 0x1017;
      assert s1.Peek(12) == 0x104;
      assert s1.Peek(13) == 0x109;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0fcc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s604(s5, gas - 1)
      else
        ExecuteFromCFGNode_s603(s5, gas - 1)
  }

  /** Node 603
    * Segment Id for this node is: 197
    * Starting at 0xfc9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s603(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x1017

    requires s0.stack[11] == 0x104

    requires s0.stack[12] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfdd;
      assert s1.Peek(6) == 0x1017;
      assert s1.Peek(12) == 0x104;
      assert s1.Peek(13) == 0x109;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 604
    * Segment Id for this node is: 198
    * Starting at 0xfcc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s604(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfdd

    requires s0.stack[5] == 0x1017

    requires s0.stack[11] == 0x104

    requires s0.stack[12] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfdd;
      assert s1.Peek(5) == 0x1017;
      assert s1.Peek(11) == 0x104;
      assert s1.Peek(12) == 0x109;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s605(s3, gas - 1)
  }

  /** Node 605
    * Segment Id for this node is: 200
    * Starting at 0xfdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s605(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1017

    requires s0.stack[9] == 0x104

    requires s0.stack[10] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1017;
      assert s1.Peek(9) == 0x104;
      assert s1.Peek(10) == 0x109;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s606(s6, gas - 1)
  }

  /** Node 606
    * Segment Id for this node is: 206
    * Starting at 0x1017
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s606(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1017 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x104

    requires s0.stack[7] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x104;
      assert s1.Peek(7) == 0x109;
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
      ExecuteFromCFGNode_s607(s10, gas - 1)
  }

  /** Node 607
    * Segment Id for this node is: 25
    * Starting at 0x104
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s607(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109;
      var s2 := Push2(s1, 0x0329);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s608(s3, gas - 1)
  }

  /** Node 608
    * Segment Id for this node is: 73
    * Starting at 0x329
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s608(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x329 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0333);
      var s5 := Push2(s4, 0x06a4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s609(s6, gas - 1)
  }

  /** Node 609
    * Segment Id for this node is: 111
    * Starting at 0x6a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s609(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x333

    requires s0.stack[5] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x333;
      assert s1.Peek(5) == 0x109;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s610(s7, gas - 1)
  }

  /** Node 610
    * Segment Id for this node is: 74
    * Starting at 0x333
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s610(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x333 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x109;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x06);
      var s5 := Push0(s4);
      var s6 := Swap1(s5);
      var s7 := SLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0x109;
      var s12 := Div(s11);
      var s13 := Push20(s12, 0xffffffffffffffffffffffffffffffffffffffff);
      var s14 := And(s13);
      var s15 := Push20(s14, 0xffffffffffffffffffffffffffffffffffffffff);
      var s16 := And(s15);
      var s17 := Dup2(s16);
      var s18 := Push20(s17, 0xffffffffffffffffffffffffffffffffffffffff);
      var s19 := And(s18);
      var s20 := Sub(s19);
      var s21 := Push2(s20, 0x03cc);
      assert s21.Peek(0) == 0x3cc;
      assert s21.Peek(6) == 0x109;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s612(s22, gas - 1)
      else
        ExecuteFromCFGNode_s611(s22, gas - 1)
  }

  /** Node 611
    * Segment Id for this node is: 75
    * Starting at 0x38a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s611(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(5) == 0x109;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Dup7(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x109;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(7) == 0x109;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s612(s23, gas - 1)
  }

  /** Node 612
    * Segment Id for this node is: 76
    * Starting at 0x3cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s612(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x109;
      var s2 := Push2(s1, 0x03d7);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x06ab);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s613(s7, gas - 1)
  }

  /** Node 613
    * Segment Id for this node is: 112
    * Starting at 0x6ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s613(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3d7

    requires s0.stack[8] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d7;
      assert s1.Peek(8) == 0x109;
      var s2 := Push2(s1, 0x06b8);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push2(s6, 0x0989);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s614(s8, gas - 1)
  }

  /** Node 614
    * Segment Id for this node is: 139
    * Starting at 0x989
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s614(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x989 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b8

    requires s0.stack[8] == 0x3d7

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b8;
      assert s1.Peek(8) == 0x3d7;
      assert s1.Peek(13) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x09f9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s624(s10, gas - 1)
      else
        ExecuteFromCFGNode_s615(s10, gas - 1)
  }

  /** Node 615
    * Segment Id for this node is: 140
    * Starting at 0x9bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s615(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b8

    requires s0.stack[8] == 0x3d7

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x6b8;
      assert s1.Peek(9) == 0x3d7;
      assert s1.Peek(14) == 0x109;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xe602df0500000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x09f0);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x9f0;
      assert s11.Peek(7) == 0x6b8;
      assert s11.Peek(11) == 0x3d7;
      assert s11.Peek(16) == 0x109;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s616(s13, gas - 1)
  }

  /** Node 616
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s616(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x9f0

    requires s0.stack[7] == 0x6b8

    requires s0.stack[11] == 0x3d7

    requires s0.stack[16] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9f0;
      assert s1.Peek(7) == 0x6b8;
      assert s1.Peek(11) == 0x3d7;
      assert s1.Peek(16) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0x9f0;
      assert s11.Peek(10) == 0x6b8;
      assert s11.Peek(14) == 0x3d7;
      assert s11.Peek(19) == 0x109;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s617(s14, gas - 1)
  }

  /** Node 617
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s617(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0x9f0

    requires s0.stack[11] == 0x6b8

    requires s0.stack[15] == 0x3d7

    requires s0.stack[20] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0x9f0;
      assert s1.Peek(11) == 0x6b8;
      assert s1.Peek(15) == 0x3d7;
      assert s1.Peek(20) == 0x109;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s618(s5, gas - 1)
  }

  /** Node 618
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s618(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0x9f0

    requires s0.stack[13] == 0x6b8

    requires s0.stack[17] == 0x3d7

    requires s0.stack[22] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0x9f0;
      assert s1.Peek(13) == 0x6b8;
      assert s1.Peek(17) == 0x3d7;
      assert s1.Peek(22) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s619(s6, gas - 1)
  }

  /** Node 619
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s619(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0x9f0

    requires s0.stack[16] == 0x6b8

    requires s0.stack[20] == 0x3d7

    requires s0.stack[25] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0x9f0;
      assert s1.Peek(16) == 0x6b8;
      assert s1.Peek(20) == 0x3d7;
      assert s1.Peek(25) == 0x109;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s620(s11, gas - 1)
  }

  /** Node 620
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s620(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0x9f0

    requires s0.stack[15] == 0x6b8

    requires s0.stack[19] == 0x3d7

    requires s0.stack[24] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0x9f0;
      assert s1.Peek(15) == 0x6b8;
      assert s1.Peek(19) == 0x3d7;
      assert s1.Peek(24) == 0x109;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s621(s7, gas - 1)
  }

  /** Node 621
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s621(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0x9f0

    requires s0.stack[12] == 0x6b8

    requires s0.stack[16] == 0x3d7

    requires s0.stack[21] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0x9f0;
      assert s1.Peek(12) == 0x6b8;
      assert s1.Peek(16) == 0x3d7;
      assert s1.Peek(21) == 0x109;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s622(s6, gas - 1)
  }

  /** Node 622
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s622(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x9f0

    requires s0.stack[8] == 0x6b8

    requires s0.stack[12] == 0x3d7

    requires s0.stack[17] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9f0;
      assert s1.Peek(8) == 0x6b8;
      assert s1.Peek(12) == 0x3d7;
      assert s1.Peek(17) == 0x109;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s623(s6, gas - 1)
  }

  /** Node 623
    * Segment Id for this node is: 141
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s623(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x6b8

    requires s0.stack[9] == 0x3d7

    requires s0.stack[14] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x6b8;
      assert s1.Peek(9) == 0x3d7;
      assert s1.Peek(14) == 0x109;
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

  /** Node 624
    * Segment Id for this node is: 142
    * Starting at 0x9f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s624(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b8

    requires s0.stack[8] == 0x3d7

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b8;
      assert s1.Peek(8) == 0x3d7;
      assert s1.Peek(13) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0a69);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s634(s10, gas - 1)
      else
        ExecuteFromCFGNode_s625(s10, gas - 1)
  }

  /** Node 625
    * Segment Id for this node is: 143
    * Starting at 0xa2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s625(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b8

    requires s0.stack[8] == 0x3d7

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x6b8;
      assert s1.Peek(9) == 0x3d7;
      assert s1.Peek(14) == 0x109;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x94280d6200000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0a60);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xa60;
      assert s11.Peek(7) == 0x6b8;
      assert s11.Peek(11) == 0x3d7;
      assert s11.Peek(16) == 0x109;
      var s12 := Push2(s11, 0x113a);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s626(s13, gas - 1)
  }

  /** Node 626
    * Segment Id for this node is: 235
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s626(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xa60

    requires s0.stack[7] == 0x6b8

    requires s0.stack[11] == 0x3d7

    requires s0.stack[16] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa60;
      assert s1.Peek(7) == 0x6b8;
      assert s1.Peek(11) == 0x3d7;
      assert s1.Peek(16) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x114d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x114d;
      assert s11.Peek(5) == 0xa60;
      assert s11.Peek(10) == 0x6b8;
      assert s11.Peek(14) == 0x3d7;
      assert s11.Peek(19) == 0x109;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x112b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s627(s14, gas - 1)
  }

  /** Node 627
    * Segment Id for this node is: 233
    * Starting at 0x112b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s627(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x114d

    requires s0.stack[6] == 0xa60

    requires s0.stack[11] == 0x6b8

    requires s0.stack[15] == 0x3d7

    requires s0.stack[20] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114d;
      assert s1.Peek(6) == 0xa60;
      assert s1.Peek(11) == 0x6b8;
      assert s1.Peek(15) == 0x3d7;
      assert s1.Peek(20) == 0x109;
      var s2 := Push2(s1, 0x1134);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s628(s5, gas - 1)
  }

  /** Node 628
    * Segment Id for this node is: 186
    * Starting at 0xf75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s628(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x1134

    requires s0.stack[4] == 0x114d

    requires s0.stack[8] == 0xa60

    requires s0.stack[13] == 0x6b8

    requires s0.stack[17] == 0x3d7

    requires s0.stack[22] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1134;
      assert s1.Peek(4) == 0x114d;
      assert s1.Peek(8) == 0xa60;
      assert s1.Peek(13) == 0x6b8;
      assert s1.Peek(17) == 0x3d7;
      assert s1.Peek(22) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f7f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0f56);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s629(s6, gas - 1)
  }

  /** Node 629
    * Segment Id for this node is: 185
    * Starting at 0xf56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s629(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xf7f

    requires s0.stack[4] == 0x1134

    requires s0.stack[7] == 0x114d

    requires s0.stack[11] == 0xa60

    requires s0.stack[16] == 0x6b8

    requires s0.stack[20] == 0x3d7

    requires s0.stack[25] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7f;
      assert s1.Peek(4) == 0x1134;
      assert s1.Peek(7) == 0x114d;
      assert s1.Peek(11) == 0xa60;
      assert s1.Peek(16) == 0x6b8;
      assert s1.Peek(20) == 0x3d7;
      assert s1.Peek(25) == 0x109;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s630(s11, gas - 1)
  }

  /** Node 630
    * Segment Id for this node is: 187
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s630(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x1134

    requires s0.stack[6] == 0x114d

    requires s0.stack[10] == 0xa60

    requires s0.stack[15] == 0x6b8

    requires s0.stack[19] == 0x3d7

    requires s0.stack[24] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1134;
      assert s1.Peek(6) == 0x114d;
      assert s1.Peek(10) == 0xa60;
      assert s1.Peek(15) == 0x6b8;
      assert s1.Peek(19) == 0x3d7;
      assert s1.Peek(24) == 0x109;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s631(s7, gas - 1)
  }

  /** Node 631
    * Segment Id for this node is: 234
    * Starting at 0x1134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s631(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x114d

    requires s0.stack[7] == 0xa60

    requires s0.stack[12] == 0x6b8

    requires s0.stack[16] == 0x3d7

    requires s0.stack[21] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x114d;
      assert s1.Peek(7) == 0xa60;
      assert s1.Peek(12) == 0x6b8;
      assert s1.Peek(16) == 0x3d7;
      assert s1.Peek(21) == 0x109;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s632(s6, gas - 1)
  }

  /** Node 632
    * Segment Id for this node is: 236
    * Starting at 0x114d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s632(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xa60

    requires s0.stack[8] == 0x6b8

    requires s0.stack[12] == 0x3d7

    requires s0.stack[17] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa60;
      assert s1.Peek(8) == 0x6b8;
      assert s1.Peek(12) == 0x3d7;
      assert s1.Peek(17) == 0x109;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s633(s6, gas - 1)
  }

  /** Node 633
    * Segment Id for this node is: 144
    * Starting at 0xa60
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s633(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x6b8

    requires s0.stack[9] == 0x3d7

    requires s0.stack[14] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x6b8;
      assert s1.Peek(9) == 0x3d7;
      assert s1.Peek(14) == 0x109;
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

  /** Node 634
    * Segment Id for this node is: 145
    * Starting at 0xa69
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s634(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b8

    requires s0.stack[8] == 0x3d7

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b8;
      assert s1.Peek(8) == 0x3d7;
      assert s1.Peek(13) == 0x109;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup7(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x6b8;
      assert s11.Peek(11) == 0x3d7;
      assert s11.Peek(16) == 0x109;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x6b8;
      assert s21.Peek(11) == 0x3d7;
      assert s21.Peek(16) == 0x109;
      var s22 := Dup6(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x6b8;
      assert s31.Peek(11) == 0x3d7;
      assert s31.Peek(16) == 0x109;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s635(s41, gas - 1)
  }

  /** Node 635
    * Segment Id for this node is: 146
    * Starting at 0xae7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s635(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b8

    requires s0.stack[8] == 0x3d7

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0x6b8;
      assert s1.Peek(9) == 0x3d7;
      assert s1.Peek(14) == 0x109;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0b52);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s643(s4, gas - 1)
      else
        ExecuteFromCFGNode_s636(s4, gas - 1)
  }

  /** Node 636
    * Segment Id for this node is: 147
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s636(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b8

    requires s0.stack[8] == 0x3d7

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(5) == 0x6b8;
      assert s1.Peek(9) == 0x3d7;
      assert s1.Peek(14) == 0x109;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup5(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x0b49);
      assert s11.Peek(0) == 0xb49;
      assert s11.Peek(10) == 0x6b8;
      assert s11.Peek(14) == 0x3d7;
      assert s11.Peek(19) == 0x109;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x1063);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s637(s15, gas - 1)
  }

  /** Node 637
    * Segment Id for this node is: 214
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s637(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xb49

    requires s0.stack[10] == 0x6b8

    requires s0.stack[14] == 0x3d7

    requires s0.stack[19] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb49;
      assert s1.Peek(10) == 0x6b8;
      assert s1.Peek(14) == 0x3d7;
      assert s1.Peek(19) == 0x109;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1076);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1076;
      assert s11.Peek(5) == 0xb49;
      assert s11.Peek(13) == 0x6b8;
      assert s11.Peek(17) == 0x3d7;
      assert s11.Peek(22) == 0x109;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x1054);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s638(s14, gas - 1)
  }

  /** Node 638
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s638(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x1076

    requires s0.stack[6] == 0xb49

    requires s0.stack[14] == 0x6b8

    requires s0.stack[18] == 0x3d7

    requires s0.stack[23] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1076;
      assert s1.Peek(6) == 0xb49;
      assert s1.Peek(14) == 0x6b8;
      assert s1.Peek(18) == 0x3d7;
      assert s1.Peek(23) == 0x109;
      var s2 := Push2(s1, 0x105d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fb0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s639(s5, gas - 1)
  }

  /** Node 639
    * Segment Id for this node is: 194
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s639(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x105d

    requires s0.stack[4] == 0x1076

    requires s0.stack[8] == 0xb49

    requires s0.stack[16] == 0x6b8

    requires s0.stack[20] == 0x3d7

    requires s0.stack[25] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x105d;
      assert s1.Peek(4) == 0x1076;
      assert s1.Peek(8) == 0xb49;
      assert s1.Peek(16) == 0x6b8;
      assert s1.Peek(20) == 0x3d7;
      assert s1.Peek(25) == 0x109;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s640(s9, gas - 1)
  }

  /** Node 640
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s640(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x1076

    requires s0.stack[7] == 0xb49

    requires s0.stack[15] == 0x6b8

    requires s0.stack[19] == 0x3d7

    requires s0.stack[24] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1076;
      assert s1.Peek(7) == 0xb49;
      assert s1.Peek(15) == 0x6b8;
      assert s1.Peek(19) == 0x3d7;
      assert s1.Peek(24) == 0x109;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s641(s6, gas - 1)
  }

  /** Node 641
    * Segment Id for this node is: 215
    * Starting at 0x1076
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s641(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1076 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xb49

    requires s0.stack[11] == 0x6b8

    requires s0.stack[15] == 0x3d7

    requires s0.stack[20] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb49;
      assert s1.Peek(11) == 0x6b8;
      assert s1.Peek(15) == 0x3d7;
      assert s1.Peek(20) == 0x109;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s642(s6, gas - 1)
  }

  /** Node 642
    * Segment Id for this node is: 148
    * Starting at 0xb49
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s642(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x6b8

    requires s0.stack[12] == 0x3d7

    requires s0.stack[17] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x6b8;
      assert s1.Peek(12) == 0x3d7;
      assert s1.Peek(17) == 0x109;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s643(s8, gas - 1)
  }

  /** Node 643
    * Segment Id for this node is: 149
    * Starting at 0xb52
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s643(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b8

    requires s0.stack[8] == 0x3d7

    requires s0.stack[13] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b8;
      assert s1.Peek(8) == 0x3d7;
      assert s1.Peek(13) == 0x109;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s644(s6, gas - 1)
  }

  /** Node 644
    * Segment Id for this node is: 113
    * Starting at 0x6b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s644(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3d7

    requires s0.stack[8] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d7;
      assert s1.Peek(8) == 0x109;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s645(s5, gas - 1)
  }

  /** Node 645
    * Segment Id for this node is: 77
    * Starting at 0x3d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s645(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x109;
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
      ExecuteFromCFGNode_s646(s10, gas - 1)
  }

  /** Node 646
    * Segment Id for this node is: 26
    * Starting at 0x109
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s646(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0116);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x103b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s647(s8, gas - 1)
  }

  /** Node 647
    * Segment Id for this node is: 210
    * Starting at 0x103b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s647(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x116;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x104e);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x104e;
      assert s11.Peek(5) == 0x116;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x102c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s648(s14, gas - 1)
  }

  /** Node 648
    * Segment Id for this node is: 208
    * Starting at 0x102c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s648(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x104e

    requires s0.stack[6] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x104e;
      assert s1.Peek(6) == 0x116;
      var s2 := Push2(s1, 0x1035);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1021);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s649(s5, gas - 1)
  }

  /** Node 649
    * Segment Id for this node is: 207
    * Starting at 0x1021
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s649(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1021 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1035

    requires s0.stack[4] == 0x104e

    requires s0.stack[8] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1035;
      assert s1.Peek(4) == 0x104e;
      assert s1.Peek(8) == 0x116;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s650(s11, gas - 1)
  }

  /** Node 650
    * Segment Id for this node is: 209
    * Starting at 0x1035
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s650(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x104e

    requires s0.stack[7] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x104e;
      assert s1.Peek(7) == 0x116;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s651(s6, gas - 1)
  }

  /** Node 651
    * Segment Id for this node is: 211
    * Starting at 0x104e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s651(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x116;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s652(s6, gas - 1)
  }

  /** Node 652
    * Segment Id for this node is: 27
    * Starting at 0x116
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s652(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
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

  /** Node 653
    * Segment Id for this node is: 21
    * Starting at 0xd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s653(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00d9);
      var s3 := Push2(s2, 0x0299);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s654(s4, gas - 1)
  }

  /** Node 654
    * Segment Id for this node is: 64
    * Starting at 0x299
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s654(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xd9;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x02a8);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x11be);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s655(s9, gas - 1)
  }

  /** Node 655
    * Segment Id for this node is: 244
    * Starting at 0x11be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s655(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2a8

    requires s0.stack[4] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2a8;
      assert s1.Peek(4) == 0xd9;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x2a8;
      assert s11.Peek(7) == 0xd9;
      var s12 := Push2(s11, 0x11d5);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s657(s13, gas - 1)
      else
        ExecuteFromCFGNode_s656(s13, gas - 1)
  }

  /** Node 656
    * Segment Id for this node is: 245
    * Starting at 0x11cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s656(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2a8

    requires s0.stack[6] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x2a8;
      assert s1.Peek(7) == 0xd9;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s657(s5, gas - 1)
  }

  /** Node 657
    * Segment Id for this node is: 246
    * Starting at 0x11d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s657(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2a8

    requires s0.stack[6] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2a8;
      assert s1.Peek(6) == 0xd9;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x11e8);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s660(s8, gas - 1)
      else
        ExecuteFromCFGNode_s658(s8, gas - 1)
  }

  /** Node 658
    * Segment Id for this node is: 247
    * Starting at 0x11e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s658(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2a8

    requires s0.stack[6] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x11e7);
      assert s1.Peek(0) == 0x11e7;
      assert s1.Peek(4) == 0x2a8;
      assert s1.Peek(7) == 0xd9;
      var s2 := Push2(s1, 0x1191);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s659(s3, gas - 1)
  }

  /** Node 659
    * Segment Id for this node is: 243
    * Starting at 0x1191
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s659(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x11e7

    requires s0.stack[4] == 0x2a8

    requires s0.stack[7] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11e7;
      assert s1.Peek(4) == 0x2a8;
      assert s1.Peek(7) == 0xd9;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 660
    * Segment Id for this node is: 249
    * Starting at 0x11e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s660(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2a8

    requires s0.stack[6] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2a8;
      assert s1.Peek(6) == 0xd9;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s661(s6, gas - 1)
  }

  /** Node 661
    * Segment Id for this node is: 65
    * Starting at 0x2a8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s661(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd9;
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
      assert s11.Peek(4) == 0xd9;
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
      assert s21.Peek(5) == 0xd9;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x02d4);
      assert s31.Peek(0) == 0x2d4;
      assert s31.Peek(8) == 0xd9;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x11be);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s662(s34, gas - 1)
  }

  /** Node 662
    * Segment Id for this node is: 244
    * Starting at 0x11be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s662(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x2d4

    requires s0.stack[8] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d4;
      assert s1.Peek(8) == 0xd9;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x2d4;
      assert s11.Peek(11) == 0xd9;
      var s12 := Push2(s11, 0x11d5);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s664(s13, gas - 1)
      else
        ExecuteFromCFGNode_s663(s13, gas - 1)
  }

  /** Node 663
    * Segment Id for this node is: 245
    * Starting at 0x11cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s663(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2d4

    requires s0.stack[10] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x2d4;
      assert s1.Peek(11) == 0xd9;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s664(s5, gas - 1)
  }

  /** Node 664
    * Segment Id for this node is: 246
    * Starting at 0x11d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s664(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2d4

    requires s0.stack[10] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2d4;
      assert s1.Peek(10) == 0xd9;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x11e8);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s667(s8, gas - 1)
      else
        ExecuteFromCFGNode_s665(s8, gas - 1)
  }

  /** Node 665
    * Segment Id for this node is: 247
    * Starting at 0x11e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s665(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2d4

    requires s0.stack[10] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x11e7);
      assert s1.Peek(0) == 0x11e7;
      assert s1.Peek(4) == 0x2d4;
      assert s1.Peek(11) == 0xd9;
      var s2 := Push2(s1, 0x1191);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s666(s3, gas - 1)
  }

  /** Node 666
    * Segment Id for this node is: 243
    * Starting at 0x1191
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s666(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x11e7

    requires s0.stack[4] == 0x2d4

    requires s0.stack[11] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11e7;
      assert s1.Peek(4) == 0x2d4;
      assert s1.Peek(11) == 0xd9;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 667
    * Segment Id for this node is: 249
    * Starting at 0x11e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s667(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2d4

    requires s0.stack[10] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2d4;
      assert s1.Peek(10) == 0xd9;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s668(s6, gas - 1)
  }

  /** Node 668
    * Segment Id for this node is: 66
    * Starting at 0x2d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s668(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xd9;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x031f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s671(s5, gas - 1)
      else
        ExecuteFromCFGNode_s669(s5, gas - 1)
  }

  /** Node 669
    * Segment Id for this node is: 67
    * Starting at 0x2db
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s669(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xd9;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x02f6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s688(s5, gas - 1)
      else
        ExecuteFromCFGNode_s670(s5, gas - 1)
  }

  /** Node 670
    * Segment Id for this node is: 68
    * Starting at 0x2e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s670(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0xd9;
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
      assert s11.Peek(7) == 0xd9;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x031f);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s671(s14, gas - 1)
  }

  /** Node 671
    * Segment Id for this node is: 72
    * Starting at 0x31f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s671(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xd9;
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
      ExecuteFromCFGNode_s672(s10, gas - 1)
  }

  /** Node 672
    * Segment Id for this node is: 22
    * Starting at 0xd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s672(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00e6);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0f32);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s673(s8, gas - 1)
  }

  /** Node 673
    * Segment Id for this node is: 182
    * Starting at 0xf32
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s673(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf32 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe6;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(5) == 0xe6;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0f4a);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0efa);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s674(s19, gas - 1)
  }

  /** Node 674
    * Segment Id for this node is: 177
    * Starting at 0xefa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s674(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xf4a

    requires s0.stack[6] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf4a;
      assert s1.Peek(6) == 0xe6;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f04);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0ea8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s675(s6, gas - 1)
  }

  /** Node 675
    * Segment Id for this node is: 170
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s675(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xf04

    requires s0.stack[5] == 0xf4a

    requires s0.stack[9] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf04;
      assert s1.Peek(5) == 0xf4a;
      assert s1.Peek(9) == 0xe6;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s676(s10, gas - 1)
  }

  /** Node 676
    * Segment Id for this node is: 178
    * Starting at 0xf04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s676(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xf4a

    requires s0.stack[8] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf4a;
      assert s1.Peek(8) == 0xe6;
      var s2 := Push2(s1, 0x0f0e);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0eb2);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s677(s6, gas - 1)
  }

  /** Node 677
    * Segment Id for this node is: 171
    * Starting at 0xeb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s677(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xf0e

    requires s0.stack[7] == 0xf4a

    requires s0.stack[11] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf0e;
      assert s1.Peek(7) == 0xf4a;
      assert s1.Peek(11) == 0xe6;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xf0e;
      assert s11.Peek(8) == 0xf4a;
      assert s11.Peek(12) == 0xe6;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s678(s15, gas - 1)
  }

  /** Node 678
    * Segment Id for this node is: 179
    * Starting at 0xf0e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s678(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xf4a

    requires s0.stack[9] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf4a;
      assert s1.Peek(9) == 0xe6;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0f1e);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0ec2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s679(s11, gas - 1)
  }

  /** Node 679
    * Segment Id for this node is: 172
    * Starting at 0xec2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s679(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xf1e

    requires s0.stack[8] == 0xf4a

    requires s0.stack[12] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf1e;
      assert s1.Peek(8) == 0xf4a;
      assert s1.Peek(12) == 0xe6;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s680(s2, gas - 1)
  }

  /** Node 680
    * Segment Id for this node is: 173
    * Starting at 0xec4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s680(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xf1e

    requires s0.stack[9] == 0xf4a

    requires s0.stack[13] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf1e;
      assert s1.Peek(9) == 0xf4a;
      assert s1.Peek(13) == 0xe6;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0edf);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s682(s7, gas - 1)
      else
        ExecuteFromCFGNode_s681(s7, gas - 1)
  }

  /** Node 681
    * Segment Id for this node is: 174
    * Starting at 0xecd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s681(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xf1e

    requires s0.stack[9] == 0xf4a

    requires s0.stack[13] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xf1e;
      assert s1.Peek(10) == 0xf4a;
      assert s1.Peek(14) == 0xe6;
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
      assert s11.Peek(5) == 0xf1e;
      assert s11.Peek(10) == 0xf4a;
      assert s11.Peek(14) == 0xe6;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0ec4);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s680(s15, gas - 1)
  }

  /** Node 682
    * Segment Id for this node is: 175
    * Starting at 0xedf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s682(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xf1e

    requires s0.stack[9] == 0xf4a

    requires s0.stack[13] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf1e;
      assert s1.Peek(9) == 0xf4a;
      assert s1.Peek(13) == 0xe6;
      var s2 := Push0(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s683(s11, gas - 1)
  }

  /** Node 683
    * Segment Id for this node is: 180
    * Starting at 0xf1e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s683(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xf4a

    requires s0.stack[8] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf4a;
      assert s1.Peek(8) == 0xe6;
      var s2 := Push2(s1, 0x0f27);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0eea);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s684(s5, gas - 1)
  }

  /** Node 684
    * Segment Id for this node is: 176
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s684(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xf27

    requires s0.stack[6] == 0xf4a

    requires s0.stack[10] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf27;
      assert s1.Peek(6) == 0xf4a;
      assert s1.Peek(10) == 0xe6;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xf27;
      assert s11.Peek(7) == 0xf4a;
      assert s11.Peek(11) == 0xe6;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s685(s14, gas - 1)
  }

  /** Node 685
    * Segment Id for this node is: 181
    * Starting at 0xf27
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s685(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xf4a

    requires s0.stack[9] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf4a;
      assert s1.Peek(9) == 0xe6;
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
      ExecuteFromCFGNode_s686(s11, gas - 1)
  }

  /** Node 686
    * Segment Id for this node is: 183
    * Starting at 0xf4a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s686(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xe6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe6;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s687(s8, gas - 1)
  }

  /** Node 687
    * Segment Id for this node is: 23
    * Starting at 0xe6
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s687(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6 as nat
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

  /** Node 688
    * Segment Id for this node is: 69
    * Starting at 0x2f6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s688(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xd9;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Push0(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push0(s8);
      var s10 := Keccak256(s9);
      var s11 := Swap1(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s689(s11, gas - 1)
  }

  /** Node 689
    * Segment Id for this node is: 70
    * Starting at 0x302
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s689(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x302 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xd9;
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
      assert s11.Peek(7) == 0xd9;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x0302);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s689(s16, gas - 1)
      else
        ExecuteFromCFGNode_s690(s16, gas - 1)
  }

  /** Node 690
    * Segment Id for this node is: 71
    * Starting at 0x316
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s690(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x316 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xd9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0xd9;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s671(s8, gas - 1)
  }

  /** Node 691
    * Segment Id for this node is: 20
    * Starting at 0xcd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s691(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd as nat
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
