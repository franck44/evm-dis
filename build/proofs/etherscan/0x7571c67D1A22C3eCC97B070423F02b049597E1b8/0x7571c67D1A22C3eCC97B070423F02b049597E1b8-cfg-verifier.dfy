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
      var s7 := Push2(s6, 0x004d);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s516(s8, gas - 1)
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
      var s1 := Push0(s0);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup1(s4);
      var s6 := Push4(s5, 0x3659cfe6);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0066);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s380(s9, gas - 1)
      else
        ExecuteFromCFGNode_s2(s9, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x1d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x4f1ef286);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x008e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s5, gas - 1)
      else
        ExecuteFromCFGNode_s3(s5, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x28
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x5c60da1b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00aa);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s5, gas - 1)
      else
        ExecuteFromCFGNode_s4(s5, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x33
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8f283970);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00d4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf851a440);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00fc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x005c);
      assert s1.Peek(0) == 0x5c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s7(s2, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 10
    * Starting at 0x5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0064);
      var s3 := Push2(s2, 0x0126);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s8(s4, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 35
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push2(s1, 0x012e);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s4, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 75
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x64;
      var s2 := Push2(s1, 0x0348);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s4, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x348

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x348;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s8, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x348

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x348;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x64;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s9, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x348

    requires s0.stack[3] == 0x12e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(3) == 0x12e;
      assert s1.Peek(4) == 0x64;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x348;
      assert s11.Peek(3) == 0x12e;
      assert s11.Peek(4) == 0x64;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s17, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 76
    * Starting at 0x348
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x03b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s9, gas - 1)
      else
        ExecuteFromCFGNode_s14(s9, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 77
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0aa2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s11, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 187
    * Starting at 0xaa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x3ac

    requires s0.stack[2] == 0x12e

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ac;
      assert s1.Peek(2) == 0x12e;
      assert s1.Peek(3) == 0x64;
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
      assert s11.Peek(4) == 0x3ac;
      assert s11.Peek(5) == 0x12e;
      assert s11.Peek(6) == 0x64;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ab9);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0a80);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s18, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 184
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0xab9

    requires s0.stack[4] == 0x3ac

    requires s0.stack[5] == 0x12e

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab9;
      assert s1.Peek(4) == 0x3ac;
      assert s1.Peek(5) == 0x12e;
      assert s1.Peek(6) == 0x64;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0a8c);
      var s4 := Push1(s3, 0x42);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s7, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xa8c

    requires s0.stack[5] == 0xab9

    requires s0.stack[8] == 0x3ac

    requires s0.stack[9] == 0x12e

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8c;
      assert s1.Peek(5) == 0xab9;
      assert s1.Peek(8) == 0x3ac;
      assert s1.Peek(9) == 0x12e;
      assert s1.Peek(10) == 0x64;
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
      assert s11.Peek(0) == 0xa8c;
      assert s11.Peek(6) == 0xab9;
      assert s11.Peek(9) == 0x3ac;
      assert s11.Peek(10) == 0x12e;
      assert s11.Peek(11) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s15, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 185
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xab9

    requires s0.stack[6] == 0x3ac

    requires s0.stack[7] == 0x12e

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab9;
      assert s1.Peek(6) == 0x3ac;
      assert s1.Peek(7) == 0x12e;
      assert s1.Peek(8) == 0x64;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a97);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0a0c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s7, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 183
    * Starting at 0xa0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xa97

    requires s0.stack[4] == 0xab9

    requires s0.stack[7] == 0x3ac

    requires s0.stack[8] == 0x12e

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa97;
      assert s1.Peek(4) == 0xab9;
      assert s1.Peek(7) == 0x3ac;
      assert s1.Peek(8) == 0x12e;
      assert s1.Peek(9) == 0x64;
      var s2 := Push32(s1, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa97;
      assert s11.Peek(4) == 0xab9;
      assert s11.Peek(7) == 0x3ac;
      assert s11.Peek(8) == 0x12e;
      assert s11.Peek(9) == 0x64;
      var s12 := Push32(s11, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s18, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 186
    * Starting at 0xa97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xab9

    requires s0.stack[5] == 0x3ac

    requires s0.stack[6] == 0x12e

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab9;
      assert s1.Peek(5) == 0x3ac;
      assert s1.Peek(6) == 0x12e;
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s10, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 188
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x3ac

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ac;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s7, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 78
    * Starting at 0x3ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
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

  /** Node 23
    * Segment Id for this node is: 79
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x64;
      var s2 := Push2(s1, 0x03bd);
      var s3 := Push2(s2, 0x04b6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s4, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 99
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x3bd

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bd;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s2, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 80
    * Starting at 0x3bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x64;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s2, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 36
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0139);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s5, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x139

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x64;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s5, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x64;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s8, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x139

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x139;
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x64;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s9, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x139

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x139;
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x64;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x139;
      assert s11.Peek(5) == 0x13e;
      assert s11.Peek(6) == 0x64;
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
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s5, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 37
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x64;
      var s2 := Push2(s1, 0x03cd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s3, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 83
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x64;
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
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x64;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x03e8);
      assert s21.Peek(0) == 0x3e8;
      assert s21.Peek(5) == 0x13e;
      assert s21.Peek(6) == 0x64;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s22, gas - 1)
      else
        ExecuteFromCFGNode_s34(s22, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 84
    * Starting at 0x3e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x13e;
      assert s1.Peek(5) == 0x64;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 35
    * Segment Id for this node is: 85
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x64;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 36
    * Segment Id for this node is: 30
    * Starting at 0xfc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc as nat
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
      var s5 := Push2(s4, 0x0107);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s6, gas - 1)
      else
        ExecuteFromCFGNode_s37(s6, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 31
    * Starting at 0x104
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 38
    * Segment Id for this node is: 32
    * Starting at 0x107
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0110);
      var s4 := Push2(s3, 0x02ea);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s5, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 68
    * Starting at 0x2ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x110;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Push2(s3, 0x03ec);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s5, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x2f3

    requires s0.stack[2] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(2) == 0x110;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s8, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x2f3

    requires s0.stack[5] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(5) == 0x110;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s9, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x2f3

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2f3;
      assert s1.Peek(4) == 0x110;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(4) == 0x110;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s17, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 69
    * Starting at 0x2f3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x110;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x0334);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s9, gas - 1)
      else
        ExecuteFromCFGNode_s44(s9, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 70
    * Starting at 0x326
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x326 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x032d);
      assert s1.Peek(0) == 0x32d;
      assert s1.Peek(2) == 0x110;
      var s2 := Push2(s1, 0x03ec);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s3, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x32d

    requires s0.stack[2] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x32d;
      assert s1.Peek(2) == 0x110;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s8, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x32d

    requires s0.stack[5] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x32d;
      assert s1.Peek(5) == 0x110;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s9, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x32d

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32d;
      assert s1.Peek(4) == 0x110;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x32d;
      assert s11.Peek(4) == 0x110;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s17, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 71
    * Starting at 0x32d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x110;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x033d);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s5, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 74
    * Starting at 0x33d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x110;
      var s2 := Swap1(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s3, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 33
    * Starting at 0x110
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x011d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x09e3);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s8, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 180
    * Starting at 0x9e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x11d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11d;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x09f6);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x9f6;
      assert s11.Peek(5) == 0x11d;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x09d4);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s14, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 178
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x9f6

    requires s0.stack[6] == 0x11d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9f6;
      assert s1.Peek(6) == 0x11d;
      var s2 := Push2(s1, 0x09dd);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08b0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s5, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 143
    * Starting at 0x8b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x9dd

    requires s0.stack[4] == 0x9f6

    requires s0.stack[8] == 0x11d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9dd;
      assert s1.Peek(4) == 0x9f6;
      assert s1.Peek(8) == 0x11d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x08ba);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0891);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 142
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x8ba

    requires s0.stack[4] == 0x9dd

    requires s0.stack[7] == 0x9f6

    requires s0.stack[11] == 0x11d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ba;
      assert s1.Peek(4) == 0x9dd;
      assert s1.Peek(7) == 0x9f6;
      assert s1.Peek(11) == 0x11d;
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
      ExecuteFromCFGNode_s55(s11, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 144
    * Starting at 0x8ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x9dd

    requires s0.stack[6] == 0x9f6

    requires s0.stack[10] == 0x11d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9dd;
      assert s1.Peek(6) == 0x9f6;
      assert s1.Peek(10) == 0x11d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s7, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 179
    * Starting at 0x9dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x9f6

    requires s0.stack[7] == 0x11d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9f6;
      assert s1.Peek(7) == 0x11d;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s6, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 181
    * Starting at 0x9f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x11d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s6, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 34
    * Starting at 0x11d
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d as nat
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

  /** Node 59
    * Segment Id for this node is: 72
    * Starting at 0x334
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x334 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x110;
      var s2 := Push2(s1, 0x033c);
      var s3 := Push2(s2, 0x0126);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s4, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 35
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x33c

    requires s0.stack[2] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x33c;
      assert s1.Peek(2) == 0x110;
      var s2 := Push2(s1, 0x012e);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s4, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 75
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x33c

    requires s0.stack[3] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x33c;
      assert s1.Peek(3) == 0x110;
      var s2 := Push2(s1, 0x0348);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s4, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x348

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x33c

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x348;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x33c;
      assert s1.Peek(4) == 0x110;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s8, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x348

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x33c

    requires s0.stack[7] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x348;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x33c;
      assert s1.Peek(7) == 0x110;
      var s2 := Push0(s1);
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
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x348

    requires s0.stack[3] == 0x12e

    requires s0.stack[4] == 0x33c

    requires s0.stack[6] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(3) == 0x12e;
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(6) == 0x110;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x348;
      assert s11.Peek(3) == 0x12e;
      assert s11.Peek(4) == 0x33c;
      assert s11.Peek(6) == 0x110;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s17, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 76
    * Starting at 0x348
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x33c

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x33c;
      assert s1.Peek(4) == 0x110;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x03b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s9, gas - 1)
      else
        ExecuteFromCFGNode_s66(s9, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 77
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x33c

    requires s0.stack[3] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x33c;
      assert s1.Peek(4) == 0x110;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0aa2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s11, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 187
    * Starting at 0xaa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x3ac

    requires s0.stack[2] == 0x12e

    requires s0.stack[3] == 0x33c

    requires s0.stack[5] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ac;
      assert s1.Peek(2) == 0x12e;
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(5) == 0x110;
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
      assert s11.Peek(4) == 0x3ac;
      assert s11.Peek(5) == 0x12e;
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(8) == 0x110;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ab9);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0a80);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s18, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 184
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xab9

    requires s0.stack[4] == 0x3ac

    requires s0.stack[5] == 0x12e

    requires s0.stack[6] == 0x33c

    requires s0.stack[8] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab9;
      assert s1.Peek(4) == 0x3ac;
      assert s1.Peek(5) == 0x12e;
      assert s1.Peek(6) == 0x33c;
      assert s1.Peek(8) == 0x110;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0a8c);
      var s4 := Push1(s3, 0x42);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s7, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xa8c

    requires s0.stack[5] == 0xab9

    requires s0.stack[8] == 0x3ac

    requires s0.stack[9] == 0x12e

    requires s0.stack[10] == 0x33c

    requires s0.stack[12] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8c;
      assert s1.Peek(5) == 0xab9;
      assert s1.Peek(8) == 0x3ac;
      assert s1.Peek(9) == 0x12e;
      assert s1.Peek(10) == 0x33c;
      assert s1.Peek(12) == 0x110;
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
      assert s11.Peek(0) == 0xa8c;
      assert s11.Peek(6) == 0xab9;
      assert s11.Peek(9) == 0x3ac;
      assert s11.Peek(10) == 0x12e;
      assert s11.Peek(11) == 0x33c;
      assert s11.Peek(13) == 0x110;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s15, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 185
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xab9

    requires s0.stack[6] == 0x3ac

    requires s0.stack[7] == 0x12e

    requires s0.stack[8] == 0x33c

    requires s0.stack[10] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab9;
      assert s1.Peek(6) == 0x3ac;
      assert s1.Peek(7) == 0x12e;
      assert s1.Peek(8) == 0x33c;
      assert s1.Peek(10) == 0x110;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a97);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0a0c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s7, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 183
    * Starting at 0xa0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xa97

    requires s0.stack[4] == 0xab9

    requires s0.stack[7] == 0x3ac

    requires s0.stack[8] == 0x12e

    requires s0.stack[9] == 0x33c

    requires s0.stack[11] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa97;
      assert s1.Peek(4) == 0xab9;
      assert s1.Peek(7) == 0x3ac;
      assert s1.Peek(8) == 0x12e;
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(11) == 0x110;
      var s2 := Push32(s1, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa97;
      assert s11.Peek(4) == 0xab9;
      assert s11.Peek(7) == 0x3ac;
      assert s11.Peek(8) == 0x12e;
      assert s11.Peek(9) == 0x33c;
      assert s11.Peek(11) == 0x110;
      var s12 := Push32(s11, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s18, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 186
    * Starting at 0xa97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xab9

    requires s0.stack[5] == 0x3ac

    requires s0.stack[6] == 0x12e

    requires s0.stack[7] == 0x33c

    requires s0.stack[9] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab9;
      assert s1.Peek(5) == 0x3ac;
      assert s1.Peek(6) == 0x12e;
      assert s1.Peek(7) == 0x33c;
      assert s1.Peek(9) == 0x110;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s10, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 188
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x3ac

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x33c

    requires s0.stack[7] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ac;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x33c;
      assert s1.Peek(7) == 0x110;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s7, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 78
    * Starting at 0x3ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x33c

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x33c;
      assert s1.Peek(4) == 0x110;
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

  /** Node 75
    * Segment Id for this node is: 79
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x33c

    requires s0.stack[3] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x33c;
      assert s1.Peek(3) == 0x110;
      var s2 := Push2(s1, 0x03bd);
      var s3 := Push2(s2, 0x04b6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s4, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 99
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3bd

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x33c

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bd;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x33c;
      assert s1.Peek(4) == 0x110;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s2, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 80
    * Starting at 0x3bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x33c

    requires s0.stack[3] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x33c;
      assert s1.Peek(3) == 0x110;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s2, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 36
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x33c

    requires s0.stack[2] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x33c;
      assert s1.Peek(2) == 0x110;
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0139);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s5, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x139

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x33c

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x33c;
      assert s1.Peek(4) == 0x110;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s5, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x33c

    requires s0.stack[6] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(6) == 0x110;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s8, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x139

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x33c

    requires s0.stack[9] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x139;
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x33c;
      assert s1.Peek(9) == 0x110;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s9, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x139

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x33c

    requires s0.stack[8] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x139;
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x33c;
      assert s1.Peek(8) == 0x110;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x139;
      assert s11.Peek(5) == 0x13e;
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(8) == 0x110;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s17, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x33c

    requires s0.stack[6] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(6) == 0x110;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s5, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 37
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x33c

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x33c;
      assert s1.Peek(4) == 0x110;
      var s2 := Push2(s1, 0x03cd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s3, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 83
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x33c

    requires s0.stack[4] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x33c;
      assert s1.Peek(4) == 0x110;
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
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x33c;
      assert s11.Peek(10) == 0x110;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x03e8);
      assert s21.Peek(0) == 0x3e8;
      assert s21.Peek(5) == 0x13e;
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(8) == 0x110;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s22, gas - 1)
      else
        ExecuteFromCFGNode_s86(s22, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 84
    * Starting at 0x3e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x33c

    requires s0.stack[6] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x13e;
      assert s1.Peek(5) == 0x33c;
      assert s1.Peek(7) == 0x110;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 87
    * Segment Id for this node is: 85
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x33c

    requires s0.stack[6] == 0x110

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(6) == 0x110;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 88
    * Segment Id for this node is: 25
    * Starting at 0xd4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
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
      var s5 := Push2(s4, 0x00df);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s6, gas - 1)
      else
        ExecuteFromCFGNode_s89(s6, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 26
    * Starting at 0xdc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 90
    * Segment Id for this node is: 27
    * Starting at 0xdf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00fa);
      var s4 := Push1(s3, 0x04);
      var s5 := Dup1(s4);
      var s6 := CallDataSize(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x00f5);
      assert s11.Peek(0) == 0xf5;
      assert s11.Peek(3) == 0xfa;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x08eb);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s15, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 151
    * Starting at 0x8eb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xf5

    requires s0.stack[3] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf5;
      assert s1.Peek(3) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0900);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s10, gas - 1)
      else
        ExecuteFromCFGNode_s92(s10, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 152
    * Starting at 0x8f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xf5

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x08ff);
      assert s1.Peek(0) == 0x8ff;
      assert s1.Peek(4) == 0xf5;
      assert s1.Peek(5) == 0xfa;
      var s2 := Push2(s1, 0x0889);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s3, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 140
    * Starting at 0x889
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x889 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x8ff

    requires s0.stack[4] == 0xf5

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8ff;
      assert s1.Peek(4) == 0xf5;
      assert s1.Peek(5) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 94
    * Segment Id for this node is: 154
    * Starting at 0x900
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x900 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xf5

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf5;
      assert s1.Peek(4) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x090d);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x08d7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s9, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 149
    * Starting at 0x8d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x90d

    requires s0.stack[7] == 0xf5

    requires s0.stack[8] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x90d;
      assert s1.Peek(7) == 0xf5;
      assert s1.Peek(8) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x08e5);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x08c1);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s10, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 145
    * Starting at 0x8c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x90d

    requires s0.stack[10] == 0xf5

    requires s0.stack[11] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      assert s1.Peek(5) == 0x90d;
      assert s1.Peek(10) == 0xf5;
      assert s1.Peek(11) == 0xfa;
      var s2 := Push2(s1, 0x08ca);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08b0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s5, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 143
    * Starting at 0x8b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x8ca

    requires s0.stack[3] == 0x8e5

    requires s0.stack[7] == 0x90d

    requires s0.stack[12] == 0xf5

    requires s0.stack[13] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ca;
      assert s1.Peek(3) == 0x8e5;
      assert s1.Peek(7) == 0x90d;
      assert s1.Peek(12) == 0xf5;
      assert s1.Peek(13) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x08ba);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0891);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s6, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 142
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x8ba

    requires s0.stack[4] == 0x8ca

    requires s0.stack[6] == 0x8e5

    requires s0.stack[10] == 0x90d

    requires s0.stack[15] == 0xf5

    requires s0.stack[16] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ba;
      assert s1.Peek(4) == 0x8ca;
      assert s1.Peek(6) == 0x8e5;
      assert s1.Peek(10) == 0x90d;
      assert s1.Peek(15) == 0xf5;
      assert s1.Peek(16) == 0xfa;
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
      ExecuteFromCFGNode_s99(s11, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 144
    * Starting at 0x8ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x8ca

    requires s0.stack[5] == 0x8e5

    requires s0.stack[9] == 0x90d

    requires s0.stack[14] == 0xf5

    requires s0.stack[15] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ca;
      assert s1.Peek(5) == 0x8e5;
      assert s1.Peek(9) == 0x90d;
      assert s1.Peek(14) == 0xf5;
      assert s1.Peek(15) == 0xfa;
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
    * Segment Id for this node is: 146
    * Starting at 0x8ca
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x8e5

    requires s0.stack[6] == 0x90d

    requires s0.stack[11] == 0xf5

    requires s0.stack[12] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e5;
      assert s1.Peek(6) == 0x90d;
      assert s1.Peek(11) == 0xf5;
      assert s1.Peek(12) == 0xfa;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x08d4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s5, gas - 1)
      else
        ExecuteFromCFGNode_s101(s5, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 147
    * Starting at 0x8d1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x90d

    requires s0.stack[10] == 0xf5

    requires s0.stack[11] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x8e5;
      assert s1.Peek(6) == 0x90d;
      assert s1.Peek(11) == 0xf5;
      assert s1.Peek(12) == 0xfa;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 102
    * Segment Id for this node is: 148
    * Starting at 0x8d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x90d

    requires s0.stack[10] == 0xf5

    requires s0.stack[11] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      assert s1.Peek(5) == 0x90d;
      assert s1.Peek(10) == 0xf5;
      assert s1.Peek(11) == 0xfa;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s3, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 150
    * Starting at 0x8e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x90d

    requires s0.stack[8] == 0xf5

    requires s0.stack[9] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x90d;
      assert s1.Peek(8) == 0xf5;
      assert s1.Peek(9) == 0xfa;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 155
    * Starting at 0x90d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xf5

    requires s0.stack[6] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf5;
      assert s1.Peek(6) == 0xfa;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s9, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 28
    * Starting at 0xf5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfa;
      var s2 := Push2(s1, 0x0296);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s3, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 61
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfa;
      var s2 := Push2(s1, 0x029e);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s4, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x29e

    requires s0.stack[2] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x29e;
      assert s1.Peek(2) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s8, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x29e

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x29e;
      assert s1.Peek(5) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s9, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x29e

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x29e;
      assert s1.Peek(4) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x29e;
      assert s11.Peek(4) == 0xfa;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s17, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 62
    * Starting at 0x29e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfa;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x02de);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s9, gas - 1)
      else
        ExecuteFromCFGNode_s111(s9, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 63
    * Starting at 0x2d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02d9);
      assert s1.Peek(0) == 0x2d9;
      assert s1.Peek(2) == 0xfa;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x046a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s4, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 95
    * Starting at 0x46a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x2d9

    requires s0.stack[3] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d9;
      assert s1.Peek(3) == 0xfa;
      var s2 := Push32(s1, 0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f);
      var s3 := Push2(s2, 0x0493);
      var s4 := Push2(s3, 0x03ec);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s5, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x493

    requires s0.stack[3] == 0x2d9

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x493;
      assert s1.Peek(3) == 0x2d9;
      assert s1.Peek(5) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s8, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x493

    requires s0.stack[6] == 0x2d9

    requires s0.stack[8] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x493;
      assert s1.Peek(6) == 0x2d9;
      assert s1.Peek(8) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s9, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x493

    requires s0.stack[5] == 0x2d9

    requires s0.stack[7] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x493;
      assert s1.Peek(5) == 0x2d9;
      assert s1.Peek(7) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x493;
      assert s11.Peek(5) == 0x2d9;
      assert s11.Peek(7) == 0xfa;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s17, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 96
    * Starting at 0x493
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x493 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x2d9

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2d9;
      assert s1.Peek(5) == 0xfa;
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x04a2);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x0ac0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s10, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 189
    * Starting at 0xac0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4a2

    requires s0.stack[6] == 0x2d9

    requires s0.stack[8] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4a2;
      assert s1.Peek(6) == 0x2d9;
      assert s1.Peek(8) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0ad3);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xad3;
      assert s11.Peek(6) == 0x4a2;
      assert s11.Peek(9) == 0x2d9;
      assert s11.Peek(11) == 0xfa;
      var s12 := Dup6(s11);
      var s13 := Push2(s12, 0x09d4);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s14, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 178
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xad3

    requires s0.stack[7] == 0x4a2

    requires s0.stack[10] == 0x2d9

    requires s0.stack[12] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xad3;
      assert s1.Peek(7) == 0x4a2;
      assert s1.Peek(10) == 0x2d9;
      assert s1.Peek(12) == 0xfa;
      var s2 := Push2(s1, 0x09dd);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08b0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s5, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 143
    * Starting at 0x8b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x9dd

    requires s0.stack[4] == 0xad3

    requires s0.stack[9] == 0x4a2

    requires s0.stack[12] == 0x2d9

    requires s0.stack[14] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9dd;
      assert s1.Peek(4) == 0xad3;
      assert s1.Peek(9) == 0x4a2;
      assert s1.Peek(12) == 0x2d9;
      assert s1.Peek(14) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x08ba);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0891);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s6, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 142
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x8ba

    requires s0.stack[4] == 0x9dd

    requires s0.stack[7] == 0xad3

    requires s0.stack[12] == 0x4a2

    requires s0.stack[15] == 0x2d9

    requires s0.stack[17] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ba;
      assert s1.Peek(4) == 0x9dd;
      assert s1.Peek(7) == 0xad3;
      assert s1.Peek(12) == 0x4a2;
      assert s1.Peek(15) == 0x2d9;
      assert s1.Peek(17) == 0xfa;
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
      ExecuteFromCFGNode_s121(s11, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 144
    * Starting at 0x8ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x9dd

    requires s0.stack[6] == 0xad3

    requires s0.stack[11] == 0x4a2

    requires s0.stack[14] == 0x2d9

    requires s0.stack[16] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9dd;
      assert s1.Peek(6) == 0xad3;
      assert s1.Peek(11) == 0x4a2;
      assert s1.Peek(14) == 0x2d9;
      assert s1.Peek(16) == 0xfa;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s7, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 179
    * Starting at 0x9dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xad3

    requires s0.stack[8] == 0x4a2

    requires s0.stack[11] == 0x2d9

    requires s0.stack[13] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xad3;
      assert s1.Peek(8) == 0x4a2;
      assert s1.Peek(11) == 0x2d9;
      assert s1.Peek(13) == 0xfa;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s6, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 190
    * Starting at 0xad3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x4a2

    requires s0.stack[7] == 0x2d9

    requires s0.stack[9] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4a2;
      assert s1.Peek(7) == 0x2d9;
      assert s1.Peek(9) == 0xfa;
      var s2 := Push2(s1, 0x0ae0);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x09d4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s8, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 178
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xae0

    requires s0.stack[7] == 0x4a2

    requires s0.stack[10] == 0x2d9

    requires s0.stack[12] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xae0;
      assert s1.Peek(7) == 0x4a2;
      assert s1.Peek(10) == 0x2d9;
      assert s1.Peek(12) == 0xfa;
      var s2 := Push2(s1, 0x09dd);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08b0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s5, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 143
    * Starting at 0x8b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x9dd

    requires s0.stack[4] == 0xae0

    requires s0.stack[9] == 0x4a2

    requires s0.stack[12] == 0x2d9

    requires s0.stack[14] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9dd;
      assert s1.Peek(4) == 0xae0;
      assert s1.Peek(9) == 0x4a2;
      assert s1.Peek(12) == 0x2d9;
      assert s1.Peek(14) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x08ba);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0891);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s6, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 142
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x8ba

    requires s0.stack[4] == 0x9dd

    requires s0.stack[7] == 0xae0

    requires s0.stack[12] == 0x4a2

    requires s0.stack[15] == 0x2d9

    requires s0.stack[17] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ba;
      assert s1.Peek(4) == 0x9dd;
      assert s1.Peek(7) == 0xae0;
      assert s1.Peek(12) == 0x4a2;
      assert s1.Peek(15) == 0x2d9;
      assert s1.Peek(17) == 0xfa;
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
      ExecuteFromCFGNode_s127(s11, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 144
    * Starting at 0x8ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x9dd

    requires s0.stack[6] == 0xae0

    requires s0.stack[11] == 0x4a2

    requires s0.stack[14] == 0x2d9

    requires s0.stack[16] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9dd;
      assert s1.Peek(6) == 0xae0;
      assert s1.Peek(11) == 0x4a2;
      assert s1.Peek(14) == 0x2d9;
      assert s1.Peek(16) == 0xfa;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s7, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 179
    * Starting at 0x9dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xae0

    requires s0.stack[8] == 0x4a2

    requires s0.stack[11] == 0x2d9

    requires s0.stack[13] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xae0;
      assert s1.Peek(8) == 0x4a2;
      assert s1.Peek(11) == 0x2d9;
      assert s1.Peek(13) == 0xfa;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s6, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 191
    * Starting at 0xae0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x4a2

    requires s0.stack[7] == 0x2d9

    requires s0.stack[9] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4a2;
      assert s1.Peek(7) == 0x2d9;
      assert s1.Peek(9) == 0xfa;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s7, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 97
    * Starting at 0x4a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x2d9

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2d9;
      assert s1.Peek(5) == 0xfa;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log1(s7);
      var s9 := Push2(s8, 0x04b3);
      var s10 := Dup2(s9);
      var s11 := Push2(s10, 0x0590);
      assert s11.Peek(0) == 0x590;
      assert s11.Peek(2) == 0x4b3;
      assert s11.Peek(4) == 0x2d9;
      assert s11.Peek(6) == 0xfa;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s12, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 107
    * Starting at 0x590
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x590 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x4b3

    requires s0.stack[3] == 0x2d9

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b3;
      assert s1.Peek(3) == 0x2d9;
      assert s1.Peek(5) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x05fe);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s10, gas - 1)
      else
        ExecuteFromCFGNode_s132(s10, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 108
    * Starting at 0x5c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x4b3

    requires s0.stack[3] == 0x2d9

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x4b3;
      assert s1.Peek(4) == 0x2d9;
      assert s1.Peek(6) == 0xfa;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x05f5);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0b57);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s11, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 196
    * Starting at 0xb57
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x5f5

    requires s0.stack[3] == 0x4b3

    requires s0.stack[5] == 0x2d9

    requires s0.stack[7] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5f5;
      assert s1.Peek(3) == 0x4b3;
      assert s1.Peek(5) == 0x2d9;
      assert s1.Peek(7) == 0xfa;
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
      assert s11.Peek(4) == 0x5f5;
      assert s11.Peek(6) == 0x4b3;
      assert s11.Peek(8) == 0x2d9;
      assert s11.Peek(10) == 0xfa;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0b6e);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0b35);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s18, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 193
    * Starting at 0xb35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xb6e

    requires s0.stack[4] == 0x5f5

    requires s0.stack[6] == 0x4b3

    requires s0.stack[8] == 0x2d9

    requires s0.stack[10] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb6e;
      assert s1.Peek(4) == 0x5f5;
      assert s1.Peek(6) == 0x4b3;
      assert s1.Peek(8) == 0x2d9;
      assert s1.Peek(10) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0b41);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s7, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xb41

    requires s0.stack[5] == 0xb6e

    requires s0.stack[8] == 0x5f5

    requires s0.stack[10] == 0x4b3

    requires s0.stack[12] == 0x2d9

    requires s0.stack[14] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb41;
      assert s1.Peek(5) == 0xb6e;
      assert s1.Peek(8) == 0x5f5;
      assert s1.Peek(10) == 0x4b3;
      assert s1.Peek(12) == 0x2d9;
      assert s1.Peek(14) == 0xfa;
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
      assert s11.Peek(0) == 0xb41;
      assert s11.Peek(6) == 0xb6e;
      assert s11.Peek(9) == 0x5f5;
      assert s11.Peek(11) == 0x4b3;
      assert s11.Peek(13) == 0x2d9;
      assert s11.Peek(15) == 0xfa;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s15, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 194
    * Starting at 0xb41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xb6e

    requires s0.stack[6] == 0x5f5

    requires s0.stack[8] == 0x4b3

    requires s0.stack[10] == 0x2d9

    requires s0.stack[12] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb6e;
      assert s1.Peek(6) == 0x5f5;
      assert s1.Peek(8) == 0x4b3;
      assert s1.Peek(10) == 0x2d9;
      assert s1.Peek(12) == 0xfa;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0b4c);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0ae7);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s7, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 192
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xb4c

    requires s0.stack[4] == 0xb6e

    requires s0.stack[7] == 0x5f5

    requires s0.stack[9] == 0x4b3

    requires s0.stack[11] == 0x2d9

    requires s0.stack[13] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb4c;
      assert s1.Peek(4) == 0xb6e;
      assert s1.Peek(7) == 0x5f5;
      assert s1.Peek(9) == 0x4b3;
      assert s1.Peek(11) == 0x2d9;
      assert s1.Peek(13) == 0xfa;
      var s2 := Push32(s1, 0x455243313936373a206e65772061646d696e20697320746865207a65726f2061);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6464726573730000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xb4c;
      assert s11.Peek(4) == 0xb6e;
      assert s11.Peek(7) == 0x5f5;
      assert s11.Peek(9) == 0x4b3;
      assert s11.Peek(11) == 0x2d9;
      assert s11.Peek(13) == 0xfa;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s13, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 195
    * Starting at 0xb4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xb6e

    requires s0.stack[5] == 0x5f5

    requires s0.stack[7] == 0x4b3

    requires s0.stack[9] == 0x2d9

    requires s0.stack[11] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb6e;
      assert s1.Peek(5) == 0x5f5;
      assert s1.Peek(7) == 0x4b3;
      assert s1.Peek(9) == 0x2d9;
      assert s1.Peek(11) == 0xfa;
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
      ExecuteFromCFGNode_s139(s10, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 197
    * Starting at 0xb6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5f5

    requires s0.stack[5] == 0x4b3

    requires s0.stack[7] == 0x2d9

    requires s0.stack[9] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5f5;
      assert s1.Peek(5) == 0x4b3;
      assert s1.Peek(7) == 0x2d9;
      assert s1.Peek(9) == 0xfa;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s7, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 109
    * Starting at 0x5f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x4b3

    requires s0.stack[4] == 0x2d9

    requires s0.stack[6] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4b3;
      assert s1.Peek(4) == 0x2d9;
      assert s1.Peek(6) == 0xfa;
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
    * Segment Id for this node is: 110
    * Starting at 0x5fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x4b3

    requires s0.stack[3] == 0x2d9

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b3;
      assert s1.Peek(3) == 0x2d9;
      assert s1.Peek(5) == 0xfa;
      var s2 := Dup1(s1);
      var s3 := Push2(s2, 0x062a);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s8, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x62a

    requires s0.stack[4] == 0x4b3

    requires s0.stack[6] == 0x2d9

    requires s0.stack[8] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x62a;
      assert s1.Peek(4) == 0x4b3;
      assert s1.Peek(6) == 0x2d9;
      assert s1.Peek(8) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s9, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 111
    * Starting at 0x62a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4b3

    requires s0.stack[5] == 0x2d9

    requires s0.stack[7] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4b3;
      assert s1.Peek(5) == 0x2d9;
      assert s1.Peek(7) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Push2(s4, 0x0100);
      var s6 := Exp(s5);
      var s7 := Dup2(s6);
      var s8 := SLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := Mul(s10);
      assert s11.Peek(6) == 0x4b3;
      assert s11.Peek(8) == 0x2d9;
      assert s11.Peek(10) == 0xfa;
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
      assert s21.Peek(2) == 0x4b3;
      assert s21.Peek(4) == 0x2d9;
      assert s21.Peek(6) == 0xfa;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s24, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 98
    * Starting at 0x4b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x2d9

    requires s0.stack[3] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d9;
      assert s1.Peek(3) == 0xfa;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s3, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 64
    * Starting at 0x2d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfa;
      var s2 := Push2(s1, 0x02e7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s3, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 67
    * Starting at 0x2e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfa;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s3, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 29
    * Starting at 0xfa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa as nat
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

  /** Node 148
    * Segment Id for this node is: 65
    * Starting at 0x2de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfa;
      var s2 := Push2(s1, 0x02e6);
      var s3 := Push2(s2, 0x0126);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s4, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 35
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x2e6

    requires s0.stack[2] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2e6;
      assert s1.Peek(2) == 0xfa;
      var s2 := Push2(s1, 0x012e);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s4, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 75
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x2e6

    requires s0.stack[3] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x2e6;
      assert s1.Peek(3) == 0xfa;
      var s2 := Push2(s1, 0x0348);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s4, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x348

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x2e6

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x348;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x2e6;
      assert s1.Peek(4) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s8, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x348

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x2e6

    requires s0.stack[7] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x348;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x2e6;
      assert s1.Peek(7) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s9, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x348

    requires s0.stack[3] == 0x12e

    requires s0.stack[4] == 0x2e6

    requires s0.stack[6] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(3) == 0x12e;
      assert s1.Peek(4) == 0x2e6;
      assert s1.Peek(6) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x348;
      assert s11.Peek(3) == 0x12e;
      assert s11.Peek(4) == 0x2e6;
      assert s11.Peek(6) == 0xfa;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s17, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 76
    * Starting at 0x348
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x2e6

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x2e6;
      assert s1.Peek(4) == 0xfa;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x03b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s9, gas - 1)
      else
        ExecuteFromCFGNode_s155(s9, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 77
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x2e6

    requires s0.stack[3] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x2e6;
      assert s1.Peek(4) == 0xfa;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0aa2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s11, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 187
    * Starting at 0xaa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x3ac

    requires s0.stack[2] == 0x12e

    requires s0.stack[3] == 0x2e6

    requires s0.stack[5] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ac;
      assert s1.Peek(2) == 0x12e;
      assert s1.Peek(3) == 0x2e6;
      assert s1.Peek(5) == 0xfa;
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
      assert s11.Peek(4) == 0x3ac;
      assert s11.Peek(5) == 0x12e;
      assert s11.Peek(6) == 0x2e6;
      assert s11.Peek(8) == 0xfa;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ab9);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0a80);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s18, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 184
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xab9

    requires s0.stack[4] == 0x3ac

    requires s0.stack[5] == 0x12e

    requires s0.stack[6] == 0x2e6

    requires s0.stack[8] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab9;
      assert s1.Peek(4) == 0x3ac;
      assert s1.Peek(5) == 0x12e;
      assert s1.Peek(6) == 0x2e6;
      assert s1.Peek(8) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0a8c);
      var s4 := Push1(s3, 0x42);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s7, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xa8c

    requires s0.stack[5] == 0xab9

    requires s0.stack[8] == 0x3ac

    requires s0.stack[9] == 0x12e

    requires s0.stack[10] == 0x2e6

    requires s0.stack[12] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8c;
      assert s1.Peek(5) == 0xab9;
      assert s1.Peek(8) == 0x3ac;
      assert s1.Peek(9) == 0x12e;
      assert s1.Peek(10) == 0x2e6;
      assert s1.Peek(12) == 0xfa;
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
      assert s11.Peek(0) == 0xa8c;
      assert s11.Peek(6) == 0xab9;
      assert s11.Peek(9) == 0x3ac;
      assert s11.Peek(10) == 0x12e;
      assert s11.Peek(11) == 0x2e6;
      assert s11.Peek(13) == 0xfa;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s15, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 185
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xab9

    requires s0.stack[6] == 0x3ac

    requires s0.stack[7] == 0x12e

    requires s0.stack[8] == 0x2e6

    requires s0.stack[10] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab9;
      assert s1.Peek(6) == 0x3ac;
      assert s1.Peek(7) == 0x12e;
      assert s1.Peek(8) == 0x2e6;
      assert s1.Peek(10) == 0xfa;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a97);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0a0c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s7, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 183
    * Starting at 0xa0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xa97

    requires s0.stack[4] == 0xab9

    requires s0.stack[7] == 0x3ac

    requires s0.stack[8] == 0x12e

    requires s0.stack[9] == 0x2e6

    requires s0.stack[11] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa97;
      assert s1.Peek(4) == 0xab9;
      assert s1.Peek(7) == 0x3ac;
      assert s1.Peek(8) == 0x12e;
      assert s1.Peek(9) == 0x2e6;
      assert s1.Peek(11) == 0xfa;
      var s2 := Push32(s1, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa97;
      assert s11.Peek(4) == 0xab9;
      assert s11.Peek(7) == 0x3ac;
      assert s11.Peek(8) == 0x12e;
      assert s11.Peek(9) == 0x2e6;
      assert s11.Peek(11) == 0xfa;
      var s12 := Push32(s11, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s18, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 186
    * Starting at 0xa97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xab9

    requires s0.stack[5] == 0x3ac

    requires s0.stack[6] == 0x12e

    requires s0.stack[7] == 0x2e6

    requires s0.stack[9] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab9;
      assert s1.Peek(5) == 0x3ac;
      assert s1.Peek(6) == 0x12e;
      assert s1.Peek(7) == 0x2e6;
      assert s1.Peek(9) == 0xfa;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s10, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 188
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x3ac

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x2e6

    requires s0.stack[7] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ac;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x2e6;
      assert s1.Peek(7) == 0xfa;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s7, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 78
    * Starting at 0x3ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x2e6

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x2e6;
      assert s1.Peek(4) == 0xfa;
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

  /** Node 164
    * Segment Id for this node is: 79
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x2e6

    requires s0.stack[3] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x2e6;
      assert s1.Peek(3) == 0xfa;
      var s2 := Push2(s1, 0x03bd);
      var s3 := Push2(s2, 0x04b6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s4, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 99
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3bd

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x2e6

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bd;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x2e6;
      assert s1.Peek(4) == 0xfa;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s2, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 80
    * Starting at 0x3bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x2e6

    requires s0.stack[3] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x2e6;
      assert s1.Peek(3) == 0xfa;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s2, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 36
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x2e6

    requires s0.stack[2] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2e6;
      assert s1.Peek(2) == 0xfa;
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0139);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s5, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x139

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x2e6

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x2e6;
      assert s1.Peek(4) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s5, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x2e6

    requires s0.stack[6] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x2e6;
      assert s1.Peek(6) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s8, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x139

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x2e6

    requires s0.stack[9] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x139;
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x2e6;
      assert s1.Peek(9) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s9, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x139

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x2e6

    requires s0.stack[8] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x139;
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x2e6;
      assert s1.Peek(8) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x139;
      assert s11.Peek(5) == 0x13e;
      assert s11.Peek(6) == 0x2e6;
      assert s11.Peek(8) == 0xfa;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s17, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x2e6

    requires s0.stack[6] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x2e6;
      assert s1.Peek(6) == 0xfa;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s5, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 37
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x2e6

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x2e6;
      assert s1.Peek(4) == 0xfa;
      var s2 := Push2(s1, 0x03cd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s3, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 83
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x2e6

    requires s0.stack[4] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x2e6;
      assert s1.Peek(4) == 0xfa;
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
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x2e6;
      assert s11.Peek(10) == 0xfa;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x03e8);
      assert s21.Peek(0) == 0x3e8;
      assert s21.Peek(5) == 0x13e;
      assert s21.Peek(6) == 0x2e6;
      assert s21.Peek(8) == 0xfa;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s22, gas - 1)
      else
        ExecuteFromCFGNode_s175(s22, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 84
    * Starting at 0x3e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x2e6

    requires s0.stack[6] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x13e;
      assert s1.Peek(5) == 0x2e6;
      assert s1.Peek(7) == 0xfa;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 176
    * Segment Id for this node is: 85
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x2e6

    requires s0.stack[6] == 0xfa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x2e6;
      assert s1.Peek(6) == 0xfa;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 177
    * Segment Id for this node is: 20
    * Starting at 0xaa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa as nat
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
      var s5 := Push2(s4, 0x00b5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s6, gas - 1)
      else
        ExecuteFromCFGNode_s178(s6, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 21
    * Starting at 0xb2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 179
    * Segment Id for this node is: 22
    * Starting at 0xb5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00be);
      var s4 := Push2(s3, 0x0240);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s5, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 54
    * Starting at 0x240
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x240 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0249);
      var s4 := Push2(s3, 0x03ec);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s5, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x249

    requires s0.stack[2] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x249;
      assert s1.Peek(2) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s8, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x249

    requires s0.stack[5] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x249;
      assert s1.Peek(5) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s9, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x249

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x249;
      assert s1.Peek(4) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x249;
      assert s11.Peek(4) == 0xbe;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s17, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 55
    * Starting at 0x249
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x249 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbe;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x028a);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s9, gas - 1)
      else
        ExecuteFromCFGNode_s185(s9, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 56
    * Starting at 0x27c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0283);
      assert s1.Peek(0) == 0x283;
      assert s1.Peek(2) == 0xbe;
      var s2 := Push2(s1, 0x03bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s3, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x283

    requires s0.stack[2] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x283;
      assert s1.Peek(2) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s5, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x283

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x283;
      assert s1.Peek(4) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s8, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x283

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x283;
      assert s1.Peek(7) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s9, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x283

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x283;
      assert s1.Peek(6) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x283;
      assert s11.Peek(6) == 0xbe;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s17, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x283

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x283;
      assert s1.Peek(4) == 0xbe;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s5, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 57
    * Starting at 0x283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbe;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0293);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s5, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 60
    * Starting at 0x293
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbe;
      var s2 := Swap1(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s3, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 23
    * Starting at 0xbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00cb);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x09e3);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s8, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 180
    * Starting at 0x9e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x09f6);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x9f6;
      assert s11.Peek(5) == 0xcb;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x09d4);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s14, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 178
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x9f6

    requires s0.stack[6] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9f6;
      assert s1.Peek(6) == 0xcb;
      var s2 := Push2(s1, 0x09dd);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08b0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s5, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 143
    * Starting at 0x8b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x9dd

    requires s0.stack[4] == 0x9f6

    requires s0.stack[8] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9dd;
      assert s1.Peek(4) == 0x9f6;
      assert s1.Peek(8) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x08ba);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0891);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s6, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 142
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x8ba

    requires s0.stack[4] == 0x9dd

    requires s0.stack[7] == 0x9f6

    requires s0.stack[11] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ba;
      assert s1.Peek(4) == 0x9dd;
      assert s1.Peek(7) == 0x9f6;
      assert s1.Peek(11) == 0xcb;
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
      ExecuteFromCFGNode_s198(s11, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 144
    * Starting at 0x8ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x9dd

    requires s0.stack[6] == 0x9f6

    requires s0.stack[10] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9dd;
      assert s1.Peek(6) == 0x9f6;
      assert s1.Peek(10) == 0xcb;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s7, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 179
    * Starting at 0x9dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x9f6

    requires s0.stack[7] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9f6;
      assert s1.Peek(7) == 0xcb;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s6, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 181
    * Starting at 0x9f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcb;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s6, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 24
    * Starting at 0xcb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
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

  /** Node 202
    * Segment Id for this node is: 58
    * Starting at 0x28a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbe;
      var s2 := Push2(s1, 0x0292);
      var s3 := Push2(s2, 0x0126);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s4, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 35
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x292

    requires s0.stack[2] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x292;
      assert s1.Peek(2) == 0xbe;
      var s2 := Push2(s1, 0x012e);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s4, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 75
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x292

    requires s0.stack[3] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x292;
      assert s1.Peek(3) == 0xbe;
      var s2 := Push2(s1, 0x0348);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s4, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x348

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x292

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x348;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(4) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s8, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x348

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x292

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x348;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x292;
      assert s1.Peek(7) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s9, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x348

    requires s0.stack[3] == 0x12e

    requires s0.stack[4] == 0x292

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(3) == 0x12e;
      assert s1.Peek(4) == 0x292;
      assert s1.Peek(6) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x348;
      assert s11.Peek(3) == 0x12e;
      assert s11.Peek(4) == 0x292;
      assert s11.Peek(6) == 0xbe;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s17, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 76
    * Starting at 0x348
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x292

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(4) == 0xbe;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x03b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s9, gas - 1)
      else
        ExecuteFromCFGNode_s209(s9, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 77
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x292

    requires s0.stack[3] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(4) == 0xbe;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0aa2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s11, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 187
    * Starting at 0xaa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x3ac

    requires s0.stack[2] == 0x12e

    requires s0.stack[3] == 0x292

    requires s0.stack[5] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ac;
      assert s1.Peek(2) == 0x12e;
      assert s1.Peek(3) == 0x292;
      assert s1.Peek(5) == 0xbe;
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
      assert s11.Peek(4) == 0x3ac;
      assert s11.Peek(5) == 0x12e;
      assert s11.Peek(6) == 0x292;
      assert s11.Peek(8) == 0xbe;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ab9);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0a80);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s18, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 184
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xab9

    requires s0.stack[4] == 0x3ac

    requires s0.stack[5] == 0x12e

    requires s0.stack[6] == 0x292

    requires s0.stack[8] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab9;
      assert s1.Peek(4) == 0x3ac;
      assert s1.Peek(5) == 0x12e;
      assert s1.Peek(6) == 0x292;
      assert s1.Peek(8) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0a8c);
      var s4 := Push1(s3, 0x42);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s7, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xa8c

    requires s0.stack[5] == 0xab9

    requires s0.stack[8] == 0x3ac

    requires s0.stack[9] == 0x12e

    requires s0.stack[10] == 0x292

    requires s0.stack[12] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8c;
      assert s1.Peek(5) == 0xab9;
      assert s1.Peek(8) == 0x3ac;
      assert s1.Peek(9) == 0x12e;
      assert s1.Peek(10) == 0x292;
      assert s1.Peek(12) == 0xbe;
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
      assert s11.Peek(0) == 0xa8c;
      assert s11.Peek(6) == 0xab9;
      assert s11.Peek(9) == 0x3ac;
      assert s11.Peek(10) == 0x12e;
      assert s11.Peek(11) == 0x292;
      assert s11.Peek(13) == 0xbe;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s15, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 185
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xab9

    requires s0.stack[6] == 0x3ac

    requires s0.stack[7] == 0x12e

    requires s0.stack[8] == 0x292

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab9;
      assert s1.Peek(6) == 0x3ac;
      assert s1.Peek(7) == 0x12e;
      assert s1.Peek(8) == 0x292;
      assert s1.Peek(10) == 0xbe;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a97);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0a0c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s7, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 183
    * Starting at 0xa0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xa97

    requires s0.stack[4] == 0xab9

    requires s0.stack[7] == 0x3ac

    requires s0.stack[8] == 0x12e

    requires s0.stack[9] == 0x292

    requires s0.stack[11] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa97;
      assert s1.Peek(4) == 0xab9;
      assert s1.Peek(7) == 0x3ac;
      assert s1.Peek(8) == 0x12e;
      assert s1.Peek(9) == 0x292;
      assert s1.Peek(11) == 0xbe;
      var s2 := Push32(s1, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa97;
      assert s11.Peek(4) == 0xab9;
      assert s11.Peek(7) == 0x3ac;
      assert s11.Peek(8) == 0x12e;
      assert s11.Peek(9) == 0x292;
      assert s11.Peek(11) == 0xbe;
      var s12 := Push32(s11, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s18, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 186
    * Starting at 0xa97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xab9

    requires s0.stack[5] == 0x3ac

    requires s0.stack[6] == 0x12e

    requires s0.stack[7] == 0x292

    requires s0.stack[9] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab9;
      assert s1.Peek(5) == 0x3ac;
      assert s1.Peek(6) == 0x12e;
      assert s1.Peek(7) == 0x292;
      assert s1.Peek(9) == 0xbe;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s10, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 188
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x3ac

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x292

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ac;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x292;
      assert s1.Peek(7) == 0xbe;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s7, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 78
    * Starting at 0x3ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x292

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(4) == 0xbe;
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

  /** Node 218
    * Segment Id for this node is: 79
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x292

    requires s0.stack[3] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x292;
      assert s1.Peek(3) == 0xbe;
      var s2 := Push2(s1, 0x03bd);
      var s3 := Push2(s2, 0x04b6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s4, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 99
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3bd

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x292

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bd;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(4) == 0xbe;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s2, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 80
    * Starting at 0x3bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x292

    requires s0.stack[3] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x292;
      assert s1.Peek(3) == 0xbe;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s2, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 36
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x292

    requires s0.stack[2] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x292;
      assert s1.Peek(2) == 0xbe;
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0139);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s5, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x139

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x292

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(4) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s5, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x292

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x292;
      assert s1.Peek(6) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s8, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x139

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x292

    requires s0.stack[9] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x139;
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x292;
      assert s1.Peek(9) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s9, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x139

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x292

    requires s0.stack[8] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x139;
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x292;
      assert s1.Peek(8) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x139;
      assert s11.Peek(5) == 0x13e;
      assert s11.Peek(6) == 0x292;
      assert s11.Peek(8) == 0xbe;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s17, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x292

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x292;
      assert s1.Peek(6) == 0xbe;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s5, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 37
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x292

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(4) == 0xbe;
      var s2 := Push2(s1, 0x03cd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s3, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 83
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x292

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x292;
      assert s1.Peek(4) == 0xbe;
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
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x292;
      assert s11.Peek(10) == 0xbe;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x03e8);
      assert s21.Peek(0) == 0x3e8;
      assert s21.Peek(5) == 0x13e;
      assert s21.Peek(6) == 0x292;
      assert s21.Peek(8) == 0xbe;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s22, gas - 1)
      else
        ExecuteFromCFGNode_s229(s22, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 84
    * Starting at 0x3e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x292

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x13e;
      assert s1.Peek(5) == 0x292;
      assert s1.Peek(7) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 230
    * Segment Id for this node is: 85
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x292

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x292;
      assert s1.Peek(6) == 0xbe;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 231
    * Segment Id for this node is: 17
    * Starting at 0x8e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00a8);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x00a3);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0xa3;
      assert s11.Peek(3) == 0xa8;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0977);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s14, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 169
    * Starting at 0x977
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x977 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xa3

    requires s0.stack[3] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa3;
      assert s1.Peek(3) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x098e);
      assert s11.Peek(0) == 0x98e;
      assert s11.Peek(7) == 0xa3;
      assert s11.Peek(8) == 0xa8;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s235(s12, gas - 1)
      else
        ExecuteFromCFGNode_s233(s12, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 170
    * Starting at 0x986
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x986 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xa3

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x098d);
      assert s1.Peek(0) == 0x98d;
      assert s1.Peek(6) == 0xa3;
      assert s1.Peek(7) == 0xa8;
      var s2 := Push2(s1, 0x0889);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s3, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 140
    * Starting at 0x889
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x889 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x98d

    requires s0.stack[6] == 0xa3

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x98d;
      assert s1.Peek(6) == 0xa3;
      assert s1.Peek(7) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 235
    * Segment Id for this node is: 172
    * Starting at 0x98e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xa3

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa3;
      assert s1.Peek(6) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x099b);
      var s4 := Dup7(s3);
      var s5 := Dup3(s4);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x08d7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s9, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 149
    * Starting at 0x8d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x99b

    requires s0.stack[9] == 0xa3

    requires s0.stack[10] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x99b;
      assert s1.Peek(9) == 0xa3;
      assert s1.Peek(10) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x08e5);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x08c1);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s10, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 145
    * Starting at 0x8c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x99b

    requires s0.stack[12] == 0xa3

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      assert s1.Peek(5) == 0x99b;
      assert s1.Peek(12) == 0xa3;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push2(s1, 0x08ca);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08b0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s5, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 143
    * Starting at 0x8b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x8ca

    requires s0.stack[3] == 0x8e5

    requires s0.stack[7] == 0x99b

    requires s0.stack[14] == 0xa3

    requires s0.stack[15] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ca;
      assert s1.Peek(3) == 0x8e5;
      assert s1.Peek(7) == 0x99b;
      assert s1.Peek(14) == 0xa3;
      assert s1.Peek(15) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x08ba);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0891);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s6, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 142
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x8ba

    requires s0.stack[4] == 0x8ca

    requires s0.stack[6] == 0x8e5

    requires s0.stack[10] == 0x99b

    requires s0.stack[17] == 0xa3

    requires s0.stack[18] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ba;
      assert s1.Peek(4) == 0x8ca;
      assert s1.Peek(6) == 0x8e5;
      assert s1.Peek(10) == 0x99b;
      assert s1.Peek(17) == 0xa3;
      assert s1.Peek(18) == 0xa8;
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
      ExecuteFromCFGNode_s240(s11, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 144
    * Starting at 0x8ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x8ca

    requires s0.stack[5] == 0x8e5

    requires s0.stack[9] == 0x99b

    requires s0.stack[16] == 0xa3

    requires s0.stack[17] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ca;
      assert s1.Peek(5) == 0x8e5;
      assert s1.Peek(9) == 0x99b;
      assert s1.Peek(16) == 0xa3;
      assert s1.Peek(17) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s7, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 146
    * Starting at 0x8ca
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x8e5

    requires s0.stack[6] == 0x99b

    requires s0.stack[13] == 0xa3

    requires s0.stack[14] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e5;
      assert s1.Peek(6) == 0x99b;
      assert s1.Peek(13) == 0xa3;
      assert s1.Peek(14) == 0xa8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x08d4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s243(s5, gas - 1)
      else
        ExecuteFromCFGNode_s242(s5, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 147
    * Starting at 0x8d1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x99b

    requires s0.stack[12] == 0xa3

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x8e5;
      assert s1.Peek(6) == 0x99b;
      assert s1.Peek(13) == 0xa3;
      assert s1.Peek(14) == 0xa8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 243
    * Segment Id for this node is: 148
    * Starting at 0x8d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x99b

    requires s0.stack[12] == 0xa3

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      assert s1.Peek(5) == 0x99b;
      assert s1.Peek(12) == 0xa3;
      assert s1.Peek(13) == 0xa8;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s3, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 150
    * Starting at 0x8e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x99b

    requires s0.stack[10] == 0xa3

    requires s0.stack[11] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x99b;
      assert s1.Peek(10) == 0xa3;
      assert s1.Peek(11) == 0xa8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s6, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 173
    * Starting at 0x99b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0xa3

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xa3;
      assert s1.Peek(8) == 0xa8;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push8(s8, 0xffffffffffffffff);
      var s10 := Dup2(s9);
      var s11 := Gt(s10);
      assert s11.Peek(7) == 0xa3;
      assert s11.Peek(8) == 0xa8;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x09bc);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s14, gas - 1)
      else
        ExecuteFromCFGNode_s246(s14, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 174
    * Starting at 0x9b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xa3

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09bb);
      assert s1.Peek(0) == 0x9bb;
      assert s1.Peek(7) == 0xa3;
      assert s1.Peek(8) == 0xa8;
      var s2 := Push2(s1, 0x088d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s3, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 141
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x9bb

    requires s0.stack[7] == 0xa3

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9bb;
      assert s1.Peek(7) == 0xa3;
      assert s1.Peek(8) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 248
    * Segment Id for this node is: 176
    * Starting at 0x9bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xa3

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xa3;
      assert s1.Peek(7) == 0xa8;
      var s2 := Push2(s1, 0x09c8);
      var s3 := Dup7(s2);
      var s4 := Dup3(s3);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0922);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s8, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 159
    * Starting at 0x922
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x922 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x9c8

    requires s0.stack[9] == 0xa3

    requires s0.stack[10] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9c8;
      assert s1.Peek(9) == 0xa3;
      assert s1.Peek(10) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x0937);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s10, gas - 1)
      else
        ExecuteFromCFGNode_s250(s10, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 160
    * Starting at 0x92f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9c8

    requires s0.stack[11] == 0xa3

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0936);
      assert s1.Peek(0) == 0x936;
      assert s1.Peek(5) == 0x9c8;
      assert s1.Peek(12) == 0xa3;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push2(s1, 0x0916);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s3, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 156
    * Starting at 0x916
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x916 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x936

    requires s0.stack[5] == 0x9c8

    requires s0.stack[12] == 0xa3

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x936;
      assert s1.Peek(5) == 0x9c8;
      assert s1.Peek(12) == 0xa3;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 252
    * Segment Id for this node is: 162
    * Starting at 0x937
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x937 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9c8

    requires s0.stack[11] == 0xa3

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9c8;
      assert s1.Peek(11) == 0xa3;
      assert s1.Peek(12) == 0xa8;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0954);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s11, gas - 1)
      else
        ExecuteFromCFGNode_s253(s11, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 163
    * Starting at 0x94c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9c8

    requires s0.stack[11] == 0xa3

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0953);
      assert s1.Peek(0) == 0x953;
      assert s1.Peek(5) == 0x9c8;
      assert s1.Peek(12) == 0xa3;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push2(s1, 0x091a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s3, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 157
    * Starting at 0x91a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x953

    requires s0.stack[5] == 0x9c8

    requires s0.stack[12] == 0xa3

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x953;
      assert s1.Peek(5) == 0x9c8;
      assert s1.Peek(12) == 0xa3;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 255
    * Segment Id for this node is: 165
    * Starting at 0x954
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x954 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9c8

    requires s0.stack[11] == 0xa3

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9c8;
      assert s1.Peek(11) == 0xa3;
      assert s1.Peek(12) == 0xa8;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := Mul(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x9c8;
      assert s11.Peek(14) == 0xa3;
      assert s11.Peek(15) == 0xa8;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0970);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s16, gas - 1)
      else
        ExecuteFromCFGNode_s256(s16, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 166
    * Starting at 0x968
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x968 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9c8

    requires s0.stack[11] == 0xa3

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x096f);
      assert s1.Peek(0) == 0x96f;
      assert s1.Peek(5) == 0x9c8;
      assert s1.Peek(12) == 0xa3;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push2(s1, 0x091e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s3, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 158
    * Starting at 0x91e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x96f

    requires s0.stack[5] == 0x9c8

    requires s0.stack[12] == 0xa3

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x96f;
      assert s1.Peek(5) == 0x9c8;
      assert s1.Peek(12) == 0xa3;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 258
    * Segment Id for this node is: 168
    * Starting at 0x970
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x970 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9c8

    requires s0.stack[11] == 0xa3

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9c8;
      assert s1.Peek(11) == 0xa3;
      assert s1.Peek(12) == 0xa8;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s7, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 177
    * Starting at 0x9c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0xa3

    requires s0.stack[9] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xa3;
      assert s1.Peek(9) == 0xa8;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xa3;
      assert s11.Peek(4) == 0xa8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s12, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 18
    * Starting at 0xa3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa8;
      var s2 := Push2(s1, 0x01a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s3, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 46
    * Starting at 0x1a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa8;
      var s2 := Push2(s1, 0x01ac);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s4, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x1ac

    requires s0.stack[4] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1ac;
      assert s1.Peek(4) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s263(s8, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x1ac

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x1ac;
      assert s1.Peek(7) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s9, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1ac

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ac;
      assert s1.Peek(6) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x1ac;
      assert s11.Peek(6) == 0xa8;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s17, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 47
    * Starting at 0x1ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa8;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x0232);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s351(s9, gas - 1)
      else
        ExecuteFromCFGNode_s266(s9, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 48
    * Starting at 0x1df
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +12
    * Net Capacity Effect: -12
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x022d);
      assert s1.Peek(0) == 0x22d;
      assert s1.Peek(4) == 0xa8;
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
      assert s11.Peek(7) == 0x22d;
      assert s11.Peek(11) == 0xa8;
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
      assert s21.Peek(7) == 0x22d;
      assert s21.Peek(11) == 0xa8;
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
      assert s31.Peek(7) == 0x22d;
      assert s31.Peek(11) == 0xa8;
      var s32 := Add(s31);
      var s33 := Dup4(s32);
      var s34 := Dup4(s33);
      var s35 := Dup1(s34);
      var s36 := Dup3(s35);
      var s37 := Dup5(s36);
      var s38 := CallDataCopy(s37);
      var s39 := Push0(s38);
      var s40 := Dup2(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s267(s41, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 49
    * Starting at 0x210
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x210 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[11] == 0x22d

    requires s0.stack[15] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.Peek(10) == 0x22d;
      assert s1.Peek(14) == 0xa8;
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(9) == 0x22d;
      assert s11.Peek(13) == 0xa8;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := Swap3(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(2) == 0x22d;
      assert s21.Peek(6) == 0xa8;
      var s22 := Push1(s21, 0x01);
      var s23 := Push2(s22, 0x043f);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s24, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 88
    * Starting at 0x43f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x22d

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x22d;
      assert s1.Peek(7) == 0xa8;
      var s2 := Push2(s1, 0x0448);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0514);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s5, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 103
    * Starting at 0x514
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x514 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x448

    requires s0.stack[5] == 0x22d

    requires s0.stack[9] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x448;
      assert s1.Peek(5) == 0x22d;
      assert s1.Peek(9) == 0xa8;
      var s2 := Push2(s1, 0x051d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x066c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s5, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 112
    * Starting at 0x66c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x51d

    requires s0.stack[3] == 0x448

    requires s0.stack[7] == 0x22d

    requires s0.stack[11] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x51d;
      assert s1.Peek(3) == 0x448;
      assert s1.Peek(7) == 0x22d;
      assert s1.Peek(11) == 0xa8;
      var s2 := Push2(s1, 0x0675);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x07a4);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s5, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 124
    * Starting at 0x7a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x675

    requires s0.stack[3] == 0x51d

    requires s0.stack[5] == 0x448

    requires s0.stack[9] == 0x22d

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x675;
      assert s1.Peek(3) == 0x51d;
      assert s1.Peek(5) == 0x448;
      assert s1.Peek(9) == 0x22d;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := ExtCodeSize(s6);
      var s8 := Gt(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x675;
      assert s11.Peek(4) == 0x51d;
      assert s11.Peek(6) == 0x448;
      assert s11.Peek(10) == 0x22d;
      assert s11.Peek(14) == 0xa8;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s14, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 113
    * Starting at 0x675
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x675 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x51d

    requires s0.stack[4] == 0x448

    requires s0.stack[8] == 0x22d

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x51d;
      assert s1.Peek(4) == 0x448;
      assert s1.Peek(8) == 0x22d;
      assert s1.Peek(12) == 0xa8;
      var s2 := Push2(s1, 0x06b4);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s282(s3, gas - 1)
      else
        ExecuteFromCFGNode_s273(s3, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 114
    * Starting at 0x67a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x51d

    requires s0.stack[3] == 0x448

    requires s0.stack[7] == 0x22d

    requires s0.stack[11] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x51d;
      assert s1.Peek(4) == 0x448;
      assert s1.Peek(8) == 0x22d;
      assert s1.Peek(12) == 0xa8;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x06ab);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0be5);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s11, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 202
    * Starting at 0xbe5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x6ab

    requires s0.stack[3] == 0x51d

    requires s0.stack[5] == 0x448

    requires s0.stack[9] == 0x22d

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6ab;
      assert s1.Peek(3) == 0x51d;
      assert s1.Peek(5) == 0x448;
      assert s1.Peek(9) == 0x22d;
      assert s1.Peek(13) == 0xa8;
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
      assert s11.Peek(4) == 0x6ab;
      assert s11.Peek(6) == 0x51d;
      assert s11.Peek(8) == 0x448;
      assert s11.Peek(12) == 0x22d;
      assert s11.Peek(16) == 0xa8;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0bfc);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0bc3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s18, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 199
    * Starting at 0xbc3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xbfc

    requires s0.stack[4] == 0x6ab

    requires s0.stack[6] == 0x51d

    requires s0.stack[8] == 0x448

    requires s0.stack[12] == 0x22d

    requires s0.stack[16] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbfc;
      assert s1.Peek(4) == 0x6ab;
      assert s1.Peek(6) == 0x51d;
      assert s1.Peek(8) == 0x448;
      assert s1.Peek(12) == 0x22d;
      assert s1.Peek(16) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0bcf);
      var s4 := Push1(s3, 0x2d);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s7, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xbcf

    requires s0.stack[5] == 0xbfc

    requires s0.stack[8] == 0x6ab

    requires s0.stack[10] == 0x51d

    requires s0.stack[12] == 0x448

    requires s0.stack[16] == 0x22d

    requires s0.stack[20] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbcf;
      assert s1.Peek(5) == 0xbfc;
      assert s1.Peek(8) == 0x6ab;
      assert s1.Peek(10) == 0x51d;
      assert s1.Peek(12) == 0x448;
      assert s1.Peek(16) == 0x22d;
      assert s1.Peek(20) == 0xa8;
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
      assert s11.Peek(0) == 0xbcf;
      assert s11.Peek(6) == 0xbfc;
      assert s11.Peek(9) == 0x6ab;
      assert s11.Peek(11) == 0x51d;
      assert s11.Peek(13) == 0x448;
      assert s11.Peek(17) == 0x22d;
      assert s11.Peek(21) == 0xa8;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s15, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 200
    * Starting at 0xbcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xbfc

    requires s0.stack[6] == 0x6ab

    requires s0.stack[8] == 0x51d

    requires s0.stack[10] == 0x448

    requires s0.stack[14] == 0x22d

    requires s0.stack[18] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbfc;
      assert s1.Peek(6) == 0x6ab;
      assert s1.Peek(8) == 0x51d;
      assert s1.Peek(10) == 0x448;
      assert s1.Peek(14) == 0x22d;
      assert s1.Peek(18) == 0xa8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0bda);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0b75);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s7, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 198
    * Starting at 0xb75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xbda

    requires s0.stack[4] == 0xbfc

    requires s0.stack[7] == 0x6ab

    requires s0.stack[9] == 0x51d

    requires s0.stack[11] == 0x448

    requires s0.stack[15] == 0x22d

    requires s0.stack[19] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbda;
      assert s1.Peek(4) == 0xbfc;
      assert s1.Peek(7) == 0x6ab;
      assert s1.Peek(9) == 0x51d;
      assert s1.Peek(11) == 0x448;
      assert s1.Peek(15) == 0x22d;
      assert s1.Peek(19) == 0xa8;
      var s2 := Push32(s1, 0x455243313936373a206e657720696d706c656d656e746174696f6e206973206e);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6f74206120636f6e747261637400000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xbda;
      assert s11.Peek(4) == 0xbfc;
      assert s11.Peek(7) == 0x6ab;
      assert s11.Peek(9) == 0x51d;
      assert s11.Peek(11) == 0x448;
      assert s11.Peek(15) == 0x22d;
      assert s11.Peek(19) == 0xa8;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s13, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 201
    * Starting at 0xbda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xbfc

    requires s0.stack[5] == 0x6ab

    requires s0.stack[7] == 0x51d

    requires s0.stack[9] == 0x448

    requires s0.stack[13] == 0x22d

    requires s0.stack[17] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbfc;
      assert s1.Peek(5) == 0x6ab;
      assert s1.Peek(7) == 0x51d;
      assert s1.Peek(9) == 0x448;
      assert s1.Peek(13) == 0x22d;
      assert s1.Peek(17) == 0xa8;
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
      ExecuteFromCFGNode_s280(s10, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 203
    * Starting at 0xbfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x6ab

    requires s0.stack[5] == 0x51d

    requires s0.stack[7] == 0x448

    requires s0.stack[11] == 0x22d

    requires s0.stack[15] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6ab;
      assert s1.Peek(5) == 0x51d;
      assert s1.Peek(7) == 0x448;
      assert s1.Peek(11) == 0x22d;
      assert s1.Peek(15) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s7, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 115
    * Starting at 0x6ab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x51d

    requires s0.stack[4] == 0x448

    requires s0.stack[8] == 0x22d

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x51d;
      assert s1.Peek(4) == 0x448;
      assert s1.Peek(8) == 0x22d;
      assert s1.Peek(12) == 0xa8;
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
    * Segment Id for this node is: 116
    * Starting at 0x6b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x51d

    requires s0.stack[3] == 0x448

    requires s0.stack[7] == 0x22d

    requires s0.stack[11] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x51d;
      assert s1.Peek(3) == 0x448;
      assert s1.Peek(7) == 0x22d;
      assert s1.Peek(11) == 0xa8;
      var s2 := Dup1(s1);
      var s3 := Push2(s2, 0x06e0);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s8, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x6e0

    requires s0.stack[4] == 0x51d

    requires s0.stack[6] == 0x448

    requires s0.stack[10] == 0x22d

    requires s0.stack[14] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6e0;
      assert s1.Peek(4) == 0x51d;
      assert s1.Peek(6) == 0x448;
      assert s1.Peek(10) == 0x22d;
      assert s1.Peek(14) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s9, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 117
    * Starting at 0x6e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x51d

    requires s0.stack[5] == 0x448

    requires s0.stack[9] == 0x22d

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x51d;
      assert s1.Peek(5) == 0x448;
      assert s1.Peek(9) == 0x22d;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Push2(s4, 0x0100);
      var s6 := Exp(s5);
      var s7 := Dup2(s6);
      var s8 := SLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := Mul(s10);
      assert s11.Peek(6) == 0x51d;
      assert s11.Peek(8) == 0x448;
      assert s11.Peek(12) == 0x22d;
      assert s11.Peek(16) == 0xa8;
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
      assert s21.Peek(2) == 0x51d;
      assert s21.Peek(4) == 0x448;
      assert s21.Peek(8) == 0x22d;
      assert s21.Peek(12) == 0xa8;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s24, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 104
    * Starting at 0x51d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x448

    requires s0.stack[5] == 0x22d

    requires s0.stack[9] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x448;
      assert s1.Peek(5) == 0x22d;
      assert s1.Peek(9) == 0xa8;
      var s2 := Dup1(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push32(s4, 0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Dup1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0x448;
      assert s11.Peek(10) == 0x22d;
      assert s11.Peek(14) == 0xa8;
      var s12 := Sub(s11);
      var s13 := Swap1(s12);
      var s14 := Log2(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s16, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 89
    * Starting at 0x448
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x448 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x22d

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x22d;
      assert s1.Peek(7) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Gt(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x0454);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s288(s8, gas - 1)
      else
        ExecuteFromCFGNode_s287(s8, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 90
    * Starting at 0x452
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x452 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x22d

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x22d;
      assert s1.Peek(7) == 0xa8;
      var s2 := Dup1(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s288(s2, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 91
    * Starting at 0x454
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x454 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x22d

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x22d;
      assert s1.Peek(8) == 0xa8;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0465);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s327(s4, gas - 1)
      else
        ExecuteFromCFGNode_s289(s4, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 92
    * Starting at 0x45a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x22d

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0463);
      assert s1.Peek(0) == 0x463;
      assert s1.Peek(4) == 0x22d;
      assert s1.Peek(8) == 0xa8;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0563);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s290(s5, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 105
    * Starting at 0x563
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x563 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x463

    requires s0.stack[6] == 0x22d

    requires s0.stack[10] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x463;
      assert s1.Peek(6) == 0x22d;
      assert s1.Peek(10) == 0xa8;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0588);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x588;
      assert s11.Peek(9) == 0x463;
      assert s11.Peek(13) == 0x22d;
      assert s11.Peek(17) == 0xa8;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x27);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0d60);
      var s20 := Push1(s19, 0x27);
      var s21 := Swap2(s20);
      assert s21.Peek(6) == 0x588;
      assert s21.Peek(10) == 0x463;
      assert s21.Peek(14) == 0x22d;
      assert s21.Peek(18) == 0xa8;
      var s22 := CodeCopy(s21);
      var s23 := Push2(s22, 0x0722);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s24, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 118
    * Starting at 0x722
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x722 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x588

    requires s0.stack[7] == 0x463

    requires s0.stack[11] == 0x22d

    requires s0.stack[15] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x588;
      assert s1.Peek(7) == 0x463;
      assert s1.Peek(11) == 0x22d;
      assert s1.Peek(15) == 0xa8;
      var s2 := Push1(s1, 0x60);
      var s3 := Push0(s2);
      var s4 := Dup1(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Dup6(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x074b);
      assert s11.Peek(0) == 0x74b;
      assert s11.Peek(10) == 0x588;
      assert s11.Peek(14) == 0x463;
      assert s11.Peek(18) == 0x22d;
      assert s11.Peek(22) == 0xa8;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0c6f);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s15, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 214
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x74b

    requires s0.stack[10] == 0x588

    requires s0.stack[14] == 0x463

    requires s0.stack[18] == 0x22d

    requires s0.stack[22] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x74b;
      assert s1.Peek(10) == 0x588;
      assert s1.Peek(14) == 0x463;
      assert s1.Peek(18) == 0x22d;
      assert s1.Peek(22) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c7a);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0c3f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s293(s7, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 210
    * Starting at 0xc3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[2] == 0xc7a

    requires s0.stack[6] == 0x74b

    requires s0.stack[14] == 0x588

    requires s0.stack[18] == 0x463

    requires s0.stack[22] == 0x22d

    requires s0.stack[26] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc7a;
      assert s1.Peek(6) == 0x74b;
      assert s1.Peek(14) == 0x588;
      assert s1.Peek(18) == 0x463;
      assert s1.Peek(22) == 0x22d;
      assert s1.Peek(26) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c49);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c03);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s294(s6, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 204
    * Starting at 0xc03
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[1] == 0xc49

    requires s0.stack[5] == 0xc7a

    requires s0.stack[9] == 0x74b

    requires s0.stack[17] == 0x588

    requires s0.stack[21] == 0x463

    requires s0.stack[25] == 0x22d

    requires s0.stack[29] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc49;
      assert s1.Peek(5) == 0xc7a;
      assert s1.Peek(9) == 0x74b;
      assert s1.Peek(17) == 0x588;
      assert s1.Peek(21) == 0x463;
      assert s1.Peek(25) == 0x22d;
      assert s1.Peek(29) == 0xa8;
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
      ExecuteFromCFGNode_s295(s10, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 211
    * Starting at 0xc49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[4] == 0xc7a

    requires s0.stack[8] == 0x74b

    requires s0.stack[16] == 0x588

    requires s0.stack[20] == 0x463

    requires s0.stack[24] == 0x22d

    requires s0.stack[28] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc7a;
      assert s1.Peek(8) == 0x74b;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x22d;
      assert s1.Peek(28) == 0xa8;
      var s2 := Push2(s1, 0x0c53);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0c0d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s6, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 205
    * Starting at 0xc0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[2] == 0xc53

    requires s0.stack[7] == 0xc7a

    requires s0.stack[11] == 0x74b

    requires s0.stack[19] == 0x588

    requires s0.stack[23] == 0x463

    requires s0.stack[27] == 0x22d

    requires s0.stack[31] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc53;
      assert s1.Peek(7) == 0xc7a;
      assert s1.Peek(11) == 0x74b;
      assert s1.Peek(19) == 0x588;
      assert s1.Peek(23) == 0x463;
      assert s1.Peek(27) == 0x22d;
      assert s1.Peek(31) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s10, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 212
    * Starting at 0xc53
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0xc7a

    requires s0.stack[9] == 0x74b

    requires s0.stack[17] == 0x588

    requires s0.stack[21] == 0x463

    requires s0.stack[25] == 0x22d

    requires s0.stack[29] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc7a;
      assert s1.Peek(9) == 0x74b;
      assert s1.Peek(17) == 0x588;
      assert s1.Peek(21) == 0x463;
      assert s1.Peek(25) == 0x22d;
      assert s1.Peek(29) == 0xa8;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0c63);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0c17);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s298(s11, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 206
    * Starting at 0xc17
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[3] == 0xc63

    requires s0.stack[8] == 0xc7a

    requires s0.stack[12] == 0x74b

    requires s0.stack[20] == 0x588

    requires s0.stack[24] == 0x463

    requires s0.stack[28] == 0x22d

    requires s0.stack[32] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc63;
      assert s1.Peek(8) == 0xc7a;
      assert s1.Peek(12) == 0x74b;
      assert s1.Peek(20) == 0x588;
      assert s1.Peek(24) == 0x463;
      assert s1.Peek(28) == 0x22d;
      assert s1.Peek(32) == 0xa8;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s299(s2, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 207
    * Starting at 0xc19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 35

    requires s0.stack[4] == 0xc63

    requires s0.stack[9] == 0xc7a

    requires s0.stack[13] == 0x74b

    requires s0.stack[21] == 0x588

    requires s0.stack[25] == 0x463

    requires s0.stack[29] == 0x22d

    requires s0.stack[33] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc63;
      assert s1.Peek(9) == 0xc7a;
      assert s1.Peek(13) == 0x74b;
      assert s1.Peek(21) == 0x588;
      assert s1.Peek(25) == 0x463;
      assert s1.Peek(29) == 0x22d;
      assert s1.Peek(33) == 0xa8;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c34);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s301(s7, gas - 1)
      else
        ExecuteFromCFGNode_s300(s7, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 208
    * Starting at 0xc22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 35

    requires s0.stack[4] == 0xc63

    requires s0.stack[9] == 0xc7a

    requires s0.stack[13] == 0x74b

    requires s0.stack[21] == 0x588

    requires s0.stack[25] == 0x463

    requires s0.stack[29] == 0x22d

    requires s0.stack[33] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xc63;
      assert s1.Peek(10) == 0xc7a;
      assert s1.Peek(14) == 0x74b;
      assert s1.Peek(22) == 0x588;
      assert s1.Peek(26) == 0x463;
      assert s1.Peek(30) == 0x22d;
      assert s1.Peek(34) == 0xa8;
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
      assert s11.Peek(5) == 0xc63;
      assert s11.Peek(10) == 0xc7a;
      assert s11.Peek(14) == 0x74b;
      assert s11.Peek(22) == 0x588;
      assert s11.Peek(26) == 0x463;
      assert s11.Peek(30) == 0x22d;
      assert s11.Peek(34) == 0xa8;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0c19);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s15, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 209
    * Starting at 0xc34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 35

    requires s0.stack[4] == 0xc63

    requires s0.stack[9] == 0xc7a

    requires s0.stack[13] == 0x74b

    requires s0.stack[21] == 0x588

    requires s0.stack[25] == 0x463

    requires s0.stack[29] == 0x22d

    requires s0.stack[33] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc63;
      assert s1.Peek(9) == 0xc7a;
      assert s1.Peek(13) == 0x74b;
      assert s1.Peek(21) == 0x588;
      assert s1.Peek(25) == 0x463;
      assert s1.Peek(29) == 0x22d;
      assert s1.Peek(33) == 0xa8;
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
      ExecuteFromCFGNode_s302(s11, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 213
    * Starting at 0xc63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[4] == 0xc7a

    requires s0.stack[8] == 0x74b

    requires s0.stack[16] == 0x588

    requires s0.stack[20] == 0x463

    requires s0.stack[24] == 0x22d

    requires s0.stack[28] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc7a;
      assert s1.Peek(8) == 0x74b;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x22d;
      assert s1.Peek(28) == 0xa8;
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Swap3(s7);
      var s9 := Swap2(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0xc7a;
      assert s11.Peek(5) == 0x74b;
      assert s11.Peek(13) == 0x588;
      assert s11.Peek(17) == 0x463;
      assert s11.Peek(21) == 0x22d;
      assert s11.Peek(25) == 0xa8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s303(s12, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 215
    * Starting at 0xc7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[4] == 0x74b

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x22d

    requires s0.stack[24] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x74b;
      assert s1.Peek(12) == 0x588;
      assert s1.Peek(16) == 0x463;
      assert s1.Peek(20) == 0x22d;
      assert s1.Peek(24) == 0xa8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s11, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 119
    * Starting at 0x74b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x588

    requires s0.stack[12] == 0x463

    requires s0.stack[16] == 0x22d

    requires s0.stack[20] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x588;
      assert s1.Peek(12) == 0x463;
      assert s1.Peek(16) == 0x22d;
      assert s1.Peek(20) == 0xa8;
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
      assert s11.Peek(9) == 0x588;
      assert s11.Peek(13) == 0x463;
      assert s11.Peek(17) == 0x22d;
      assert s11.Peek(21) == 0xa8;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup1(s15);
      var s17 := Push0(s16);
      var s18 := Dup2(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x0783);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s350(s21, gas - 1)
      else
        ExecuteFromCFGNode_s305(s21, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 120
    * Starting at 0x763
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x763 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x588

    requires s0.stack[13] == 0x463

    requires s0.stack[17] == 0x22d

    requires s0.stack[21] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0x588;
      assert s1.Peek(14) == 0x463;
      assert s1.Peek(18) == 0x22d;
      assert s1.Peek(22) == 0xa8;
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
      assert s11.Peek(11) == 0x588;
      assert s11.Peek(15) == 0x463;
      assert s11.Peek(19) == 0x22d;
      assert s11.Peek(23) == 0xa8;
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
      assert s21.Peek(13) == 0x588;
      assert s21.Peek(17) == 0x463;
      assert s21.Peek(21) == 0x22d;
      assert s21.Peek(25) == 0xa8;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0788);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s25, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 122
    * Starting at 0x788
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x788 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x588

    requires s0.stack[13] == 0x463

    requires s0.stack[17] == 0x22d

    requires s0.stack[21] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x588;
      assert s1.Peek(13) == 0x463;
      assert s1.Peek(17) == 0x22d;
      assert s1.Peek(21) == 0xa8;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0799);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Dup4(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(4) == 0x799;
      assert s11.Peek(11) == 0x588;
      assert s11.Peek(15) == 0x463;
      assert s11.Peek(19) == 0x22d;
      assert s11.Peek(23) == 0xa8;
      var s12 := Push2(s11, 0x07c6);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s13, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 125
    * Starting at 0x7c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[4] == 0x799

    requires s0.stack[11] == 0x588

    requires s0.stack[15] == 0x463

    requires s0.stack[19] == 0x22d

    requires s0.stack[23] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x799;
      assert s1.Peek(11) == 0x588;
      assert s1.Peek(15) == 0x463;
      assert s1.Peek(19) == 0x22d;
      assert s1.Peek(23) == 0xa8;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0827);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s331(s6, gas - 1)
      else
        ExecuteFromCFGNode_s308(s6, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 126
    * Starting at 0x7cf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x22d

    requires s0.stack[24] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x22d;
      assert s1.Peek(25) == 0xa8;
      var s2 := Dup4(s1);
      var s3 := MLoad(s2);
      var s4 := Sub(s3);
      var s5 := Push2(s4, 0x081f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s322(s6, gas - 1)
      else
        ExecuteFromCFGNode_s309(s6, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 127
    * Starting at 0x7d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x22d

    requires s0.stack[24] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x07df);
      assert s1.Peek(0) == 0x7df;
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x22d;
      assert s1.Peek(25) == 0xa8;
      var s2 := Dup6(s1);
      var s3 := Push2(s2, 0x07a4);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s4, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 124
    * Starting at 0x7a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x7df

    requires s0.stack[7] == 0x799

    requires s0.stack[14] == 0x588

    requires s0.stack[18] == 0x463

    requires s0.stack[22] == 0x22d

    requires s0.stack[26] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7df;
      assert s1.Peek(7) == 0x799;
      assert s1.Peek(14) == 0x588;
      assert s1.Peek(18) == 0x463;
      assert s1.Peek(22) == 0x22d;
      assert s1.Peek(26) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := ExtCodeSize(s6);
      var s8 := Gt(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x7df;
      assert s11.Peek(8) == 0x799;
      assert s11.Peek(15) == 0x588;
      assert s11.Peek(19) == 0x463;
      assert s11.Peek(23) == 0x22d;
      assert s11.Peek(27) == 0xa8;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s14, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 128
    * Starting at 0x7df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[6] == 0x799

    requires s0.stack[13] == 0x588

    requires s0.stack[17] == 0x463

    requires s0.stack[21] == 0x22d

    requires s0.stack[25] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x22d;
      assert s1.Peek(25) == 0xa8;
      var s2 := Push2(s1, 0x081e);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s321(s3, gas - 1)
      else
        ExecuteFromCFGNode_s312(s3, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 129
    * Starting at 0x7e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x22d

    requires s0.stack[24] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x22d;
      assert s1.Peek(25) == 0xa8;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0815);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0ccf);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s11, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 220
    * Starting at 0xccf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x815

    requires s0.stack[7] == 0x799

    requires s0.stack[14] == 0x588

    requires s0.stack[18] == 0x463

    requires s0.stack[22] == 0x22d

    requires s0.stack[26] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x815;
      assert s1.Peek(7) == 0x799;
      assert s1.Peek(14) == 0x588;
      assert s1.Peek(18) == 0x463;
      assert s1.Peek(22) == 0x22d;
      assert s1.Peek(26) == 0xa8;
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
      assert s11.Peek(4) == 0x815;
      assert s11.Peek(10) == 0x799;
      assert s11.Peek(17) == 0x588;
      assert s11.Peek(21) == 0x463;
      assert s11.Peek(25) == 0x22d;
      assert s11.Peek(29) == 0xa8;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ce6);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0cad);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s314(s18, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 217
    * Starting at 0xcad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[1] == 0xce6

    requires s0.stack[4] == 0x815

    requires s0.stack[10] == 0x799

    requires s0.stack[17] == 0x588

    requires s0.stack[21] == 0x463

    requires s0.stack[25] == 0x22d

    requires s0.stack[29] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xce6;
      assert s1.Peek(4) == 0x815;
      assert s1.Peek(10) == 0x799;
      assert s1.Peek(17) == 0x588;
      assert s1.Peek(21) == 0x463;
      assert s1.Peek(25) == 0x22d;
      assert s1.Peek(29) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0cb9);
      var s4 := Push1(s3, 0x1d);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s7, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 35

    requires s0.stack[2] == 0xcb9

    requires s0.stack[5] == 0xce6

    requires s0.stack[8] == 0x815

    requires s0.stack[14] == 0x799

    requires s0.stack[21] == 0x588

    requires s0.stack[25] == 0x463

    requires s0.stack[29] == 0x22d

    requires s0.stack[33] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcb9;
      assert s1.Peek(5) == 0xce6;
      assert s1.Peek(8) == 0x815;
      assert s1.Peek(14) == 0x799;
      assert s1.Peek(21) == 0x588;
      assert s1.Peek(25) == 0x463;
      assert s1.Peek(29) == 0x22d;
      assert s1.Peek(33) == 0xa8;
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
      assert s11.Peek(0) == 0xcb9;
      assert s11.Peek(6) == 0xce6;
      assert s11.Peek(9) == 0x815;
      assert s11.Peek(15) == 0x799;
      assert s11.Peek(22) == 0x588;
      assert s11.Peek(26) == 0x463;
      assert s11.Peek(30) == 0x22d;
      assert s11.Peek(34) == 0xa8;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s15, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 218
    * Starting at 0xcb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[3] == 0xce6

    requires s0.stack[6] == 0x815

    requires s0.stack[12] == 0x799

    requires s0.stack[19] == 0x588

    requires s0.stack[23] == 0x463

    requires s0.stack[27] == 0x22d

    requires s0.stack[31] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xce6;
      assert s1.Peek(6) == 0x815;
      assert s1.Peek(12) == 0x799;
      assert s1.Peek(19) == 0x588;
      assert s1.Peek(23) == 0x463;
      assert s1.Peek(27) == 0x22d;
      assert s1.Peek(31) == 0xa8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0cc4);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0c85);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s317(s7, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 216
    * Starting at 0xc85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xcc4

    requires s0.stack[4] == 0xce6

    requires s0.stack[7] == 0x815

    requires s0.stack[13] == 0x799

    requires s0.stack[20] == 0x588

    requires s0.stack[24] == 0x463

    requires s0.stack[28] == 0x22d

    requires s0.stack[32] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcc4;
      assert s1.Peek(4) == 0xce6;
      assert s1.Peek(7) == 0x815;
      assert s1.Peek(13) == 0x799;
      assert s1.Peek(20) == 0x588;
      assert s1.Peek(24) == 0x463;
      assert s1.Peek(28) == 0x22d;
      assert s1.Peek(32) == 0xa8;
      var s2 := Push32(s1, 0x416464726573733a2063616c6c20746f206e6f6e2d636f6e7472616374000000);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s8, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 219
    * Starting at 0xcc4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[2] == 0xce6

    requires s0.stack[5] == 0x815

    requires s0.stack[11] == 0x799

    requires s0.stack[18] == 0x588

    requires s0.stack[22] == 0x463

    requires s0.stack[26] == 0x22d

    requires s0.stack[30] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xce6;
      assert s1.Peek(5) == 0x815;
      assert s1.Peek(11) == 0x799;
      assert s1.Peek(18) == 0x588;
      assert s1.Peek(22) == 0x463;
      assert s1.Peek(26) == 0x22d;
      assert s1.Peek(30) == 0xa8;
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
      ExecuteFromCFGNode_s319(s10, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 221
    * Starting at 0xce6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[3] == 0x815

    requires s0.stack[9] == 0x799

    requires s0.stack[16] == 0x588

    requires s0.stack[20] == 0x463

    requires s0.stack[24] == 0x22d

    requires s0.stack[28] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x815;
      assert s1.Peek(9) == 0x799;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x22d;
      assert s1.Peek(28) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s7, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 130
    * Starting at 0x815
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x815 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[6] == 0x799

    requires s0.stack[13] == 0x588

    requires s0.stack[17] == 0x463

    requires s0.stack[21] == 0x22d

    requires s0.stack[25] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x22d;
      assert s1.Peek(25) == 0xa8;
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

  /** Node 321
    * Segment Id for this node is: 131
    * Starting at 0x81e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x22d

    requires s0.stack[24] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s322(s1, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 132
    * Starting at 0x81f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x22d

    requires s0.stack[24] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x799;
      assert s1.Peek(12) == 0x588;
      assert s1.Peek(16) == 0x463;
      assert s1.Peek(20) == 0x22d;
      assert s1.Peek(24) == 0xa8;
      var s2 := Dup3(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x0832);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s6, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 135
    * Starting at 0x832
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x832 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x22d

    requires s0.stack[24] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x799;
      assert s1.Peek(12) == 0x588;
      assert s1.Peek(16) == 0x463;
      assert s1.Peek(20) == 0x22d;
      assert s1.Peek(24) == 0xa8;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s324(s8, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 123
    * Starting at 0x799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x588

    requires s0.stack[11] == 0x463

    requires s0.stack[15] == 0x22d

    requires s0.stack[19] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x588;
      assert s1.Peek(11) == 0x463;
      assert s1.Peek(15) == 0x22d;
      assert s1.Peek(19) == 0xa8;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap4(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s11, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 106
    * Starting at 0x588
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x588 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x463

    requires s0.stack[8] == 0x22d

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x463;
      assert s1.Peek(8) == 0x22d;
      assert s1.Peek(12) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s8, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 93
    * Starting at 0x463
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x22d

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x22d;
      assert s1.Peek(8) == 0xa8;
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s327(s2, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 94
    * Starting at 0x465
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x465 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x22d

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x22d;
      assert s1.Peek(7) == 0xa8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s5, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 50
    * Starting at 0x22d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa8;
      var s2 := Push2(s1, 0x023b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s329(s3, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 53
    * Starting at 0x23b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s5, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 19
    * Starting at 0xa8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8 as nat
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

  /** Node 331
    * Segment Id for this node is: 133
    * Starting at 0x827
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x827 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x22d

    requires s0.stack[24] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x799;
      assert s1.Peek(12) == 0x588;
      assert s1.Peek(16) == 0x463;
      assert s1.Peek(20) == 0x22d;
      assert s1.Peek(24) == 0xa8;
      var s2 := Push2(s1, 0x0831);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x083a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s6, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 136
    * Starting at 0x83a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0x831

    requires s0.stack[8] == 0x799

    requires s0.stack[15] == 0x588

    requires s0.stack[19] == 0x463

    requires s0.stack[23] == 0x22d

    requires s0.stack[27] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x831;
      assert s1.Peek(8) == 0x799;
      assert s1.Peek(15) == 0x588;
      assert s1.Peek(19) == 0x463;
      assert s1.Peek(23) == 0x22d;
      assert s1.Peek(27) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x084c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s334(s8, gas - 1)
      else
        ExecuteFromCFGNode_s333(s8, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 137
    * Starting at 0x844
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x844 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0x831

    requires s0.stack[8] == 0x799

    requires s0.stack[15] == 0x588

    requires s0.stack[19] == 0x463

    requires s0.stack[23] == 0x22d

    requires s0.stack[27] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(3) == 0x831;
      assert s1.Peek(9) == 0x799;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x22d;
      assert s1.Peek(28) == 0xa8;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 334
    * Segment Id for this node is: 138
    * Starting at 0x84c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0x831

    requires s0.stack[8] == 0x799

    requires s0.stack[15] == 0x588

    requires s0.stack[19] == 0x463

    requires s0.stack[23] == 0x22d

    requires s0.stack[27] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x831;
      assert s1.Peek(8) == 0x799;
      assert s1.Peek(15) == 0x588;
      assert s1.Peek(19) == 0x463;
      assert s1.Peek(23) == 0x22d;
      assert s1.Peek(27) == 0xa8;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0880);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x880;
      assert s11.Peek(5) == 0x831;
      assert s11.Peek(11) == 0x799;
      assert s11.Peek(18) == 0x588;
      assert s11.Peek(22) == 0x463;
      assert s11.Peek(26) == 0x22d;
      assert s11.Peek(30) == 0xa8;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d3f);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s14, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 229
    * Starting at 0xd3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[2] == 0x880

    requires s0.stack[5] == 0x831

    requires s0.stack[11] == 0x799

    requires s0.stack[18] == 0x588

    requires s0.stack[22] == 0x463

    requires s0.stack[26] == 0x22d

    requires s0.stack[30] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x880;
      assert s1.Peek(5) == 0x831;
      assert s1.Peek(11) == 0x799;
      assert s1.Peek(18) == 0x588;
      assert s1.Peek(22) == 0x463;
      assert s1.Peek(26) == 0x22d;
      assert s1.Peek(30) == 0xa8;
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
      assert s11.Peek(5) == 0x880;
      assert s11.Peek(8) == 0x831;
      assert s11.Peek(14) == 0x799;
      assert s11.Peek(21) == 0x588;
      assert s11.Peek(25) == 0x463;
      assert s11.Peek(29) == 0x22d;
      assert s11.Peek(33) == 0xa8;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0d57);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0d07);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s19, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 224
    * Starting at 0xd07
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd07 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 36

    requires s0.stack[2] == 0xd57

    requires s0.stack[6] == 0x880

    requires s0.stack[9] == 0x831

    requires s0.stack[15] == 0x799

    requires s0.stack[22] == 0x588

    requires s0.stack[26] == 0x463

    requires s0.stack[30] == 0x22d

    requires s0.stack[34] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd57;
      assert s1.Peek(6) == 0x880;
      assert s1.Peek(9) == 0x831;
      assert s1.Peek(15) == 0x799;
      assert s1.Peek(22) == 0x588;
      assert s1.Peek(26) == 0x463;
      assert s1.Peek(30) == 0x22d;
      assert s1.Peek(34) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d11);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0ced);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s6, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 222
    * Starting at 0xced
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xced as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[1] == 0xd11

    requires s0.stack[5] == 0xd57

    requires s0.stack[9] == 0x880

    requires s0.stack[12] == 0x831

    requires s0.stack[18] == 0x799

    requires s0.stack[25] == 0x588

    requires s0.stack[29] == 0x463

    requires s0.stack[33] == 0x22d

    requires s0.stack[37] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd11;
      assert s1.Peek(5) == 0xd57;
      assert s1.Peek(9) == 0x880;
      assert s1.Peek(12) == 0x831;
      assert s1.Peek(18) == 0x799;
      assert s1.Peek(25) == 0x588;
      assert s1.Peek(29) == 0x463;
      assert s1.Peek(33) == 0x22d;
      assert s1.Peek(37) == 0xa8;
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
      ExecuteFromCFGNode_s338(s10, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 225
    * Starting at 0xd11
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 38

    requires s0.stack[4] == 0xd57

    requires s0.stack[8] == 0x880

    requires s0.stack[11] == 0x831

    requires s0.stack[17] == 0x799

    requires s0.stack[24] == 0x588

    requires s0.stack[28] == 0x463

    requires s0.stack[32] == 0x22d

    requires s0.stack[36] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd57;
      assert s1.Peek(8) == 0x880;
      assert s1.Peek(11) == 0x831;
      assert s1.Peek(17) == 0x799;
      assert s1.Peek(24) == 0x588;
      assert s1.Peek(28) == 0x463;
      assert s1.Peek(32) == 0x22d;
      assert s1.Peek(36) == 0xa8;
      var s2 := Push2(s1, 0x0d1b);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x09fc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s6, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 41

    requires s0.stack[2] == 0xd1b

    requires s0.stack[7] == 0xd57

    requires s0.stack[11] == 0x880

    requires s0.stack[14] == 0x831

    requires s0.stack[20] == 0x799

    requires s0.stack[27] == 0x588

    requires s0.stack[31] == 0x463

    requires s0.stack[35] == 0x22d

    requires s0.stack[39] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1b;
      assert s1.Peek(7) == 0xd57;
      assert s1.Peek(11) == 0x880;
      assert s1.Peek(14) == 0x831;
      assert s1.Peek(20) == 0x799;
      assert s1.Peek(27) == 0x588;
      assert s1.Peek(31) == 0x463;
      assert s1.Peek(35) == 0x22d;
      assert s1.Peek(39) == 0xa8;
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
      assert s11.Peek(0) == 0xd1b;
      assert s11.Peek(8) == 0xd57;
      assert s11.Peek(12) == 0x880;
      assert s11.Peek(15) == 0x831;
      assert s11.Peek(21) == 0x799;
      assert s11.Peek(28) == 0x588;
      assert s11.Peek(32) == 0x463;
      assert s11.Peek(36) == 0x22d;
      assert s11.Peek(40) == 0xa8;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s340(s15, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 226
    * Starting at 0xd1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[5] == 0xd57

    requires s0.stack[9] == 0x880

    requires s0.stack[12] == 0x831

    requires s0.stack[18] == 0x799

    requires s0.stack[25] == 0x588

    requires s0.stack[29] == 0x463

    requires s0.stack[33] == 0x22d

    requires s0.stack[37] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd57;
      assert s1.Peek(9) == 0x880;
      assert s1.Peek(12) == 0x831;
      assert s1.Peek(18) == 0x799;
      assert s1.Peek(25) == 0x588;
      assert s1.Peek(29) == 0x463;
      assert s1.Peek(33) == 0x22d;
      assert s1.Peek(37) == 0xa8;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0d2b);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0c17);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s11, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 206
    * Starting at 0xc17
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 42

    requires s0.stack[3] == 0xd2b

    requires s0.stack[8] == 0xd57

    requires s0.stack[12] == 0x880

    requires s0.stack[15] == 0x831

    requires s0.stack[21] == 0x799

    requires s0.stack[28] == 0x588

    requires s0.stack[32] == 0x463

    requires s0.stack[36] == 0x22d

    requires s0.stack[40] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(8) == 0xd57;
      assert s1.Peek(12) == 0x880;
      assert s1.Peek(15) == 0x831;
      assert s1.Peek(21) == 0x799;
      assert s1.Peek(28) == 0x588;
      assert s1.Peek(32) == 0x463;
      assert s1.Peek(36) == 0x22d;
      assert s1.Peek(40) == 0xa8;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s342(s2, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 207
    * Starting at 0xc19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 43

    requires s0.stack[4] == 0xd2b

    requires s0.stack[9] == 0xd57

    requires s0.stack[13] == 0x880

    requires s0.stack[16] == 0x831

    requires s0.stack[22] == 0x799

    requires s0.stack[29] == 0x588

    requires s0.stack[33] == 0x463

    requires s0.stack[37] == 0x22d

    requires s0.stack[41] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(9) == 0xd57;
      assert s1.Peek(13) == 0x880;
      assert s1.Peek(16) == 0x831;
      assert s1.Peek(22) == 0x799;
      assert s1.Peek(29) == 0x588;
      assert s1.Peek(33) == 0x463;
      assert s1.Peek(37) == 0x22d;
      assert s1.Peek(41) == 0xa8;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c34);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s344(s7, gas - 1)
      else
        ExecuteFromCFGNode_s343(s7, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 208
    * Starting at 0xc22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 43

    requires s0.stack[4] == 0xd2b

    requires s0.stack[9] == 0xd57

    requires s0.stack[13] == 0x880

    requires s0.stack[16] == 0x831

    requires s0.stack[22] == 0x799

    requires s0.stack[29] == 0x588

    requires s0.stack[33] == 0x463

    requires s0.stack[37] == 0x22d

    requires s0.stack[41] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xd2b;
      assert s1.Peek(10) == 0xd57;
      assert s1.Peek(14) == 0x880;
      assert s1.Peek(17) == 0x831;
      assert s1.Peek(23) == 0x799;
      assert s1.Peek(30) == 0x588;
      assert s1.Peek(34) == 0x463;
      assert s1.Peek(38) == 0x22d;
      assert s1.Peek(42) == 0xa8;
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
      assert s11.Peek(5) == 0xd2b;
      assert s11.Peek(10) == 0xd57;
      assert s11.Peek(14) == 0x880;
      assert s11.Peek(17) == 0x831;
      assert s11.Peek(23) == 0x799;
      assert s11.Peek(30) == 0x588;
      assert s11.Peek(34) == 0x463;
      assert s11.Peek(38) == 0x22d;
      assert s11.Peek(42) == 0xa8;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0c19);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s15, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 209
    * Starting at 0xc34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 43

    requires s0.stack[4] == 0xd2b

    requires s0.stack[9] == 0xd57

    requires s0.stack[13] == 0x880

    requires s0.stack[16] == 0x831

    requires s0.stack[22] == 0x799

    requires s0.stack[29] == 0x588

    requires s0.stack[33] == 0x463

    requires s0.stack[37] == 0x22d

    requires s0.stack[41] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(9) == 0xd57;
      assert s1.Peek(13) == 0x880;
      assert s1.Peek(16) == 0x831;
      assert s1.Peek(22) == 0x799;
      assert s1.Peek(29) == 0x588;
      assert s1.Peek(33) == 0x463;
      assert s1.Peek(37) == 0x22d;
      assert s1.Peek(41) == 0xa8;
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
      ExecuteFromCFGNode_s345(s11, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 227
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 38

    requires s0.stack[4] == 0xd57

    requires s0.stack[8] == 0x880

    requires s0.stack[11] == 0x831

    requires s0.stack[17] == 0x799

    requires s0.stack[24] == 0x588

    requires s0.stack[28] == 0x463

    requires s0.stack[32] == 0x22d

    requires s0.stack[36] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd57;
      assert s1.Peek(8) == 0x880;
      assert s1.Peek(11) == 0x831;
      assert s1.Peek(17) == 0x799;
      assert s1.Peek(24) == 0x588;
      assert s1.Peek(28) == 0x463;
      assert s1.Peek(32) == 0x22d;
      assert s1.Peek(36) == 0xa8;
      var s2 := Push2(s1, 0x0d34);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0cf7);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s346(s5, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 223
    * Starting at 0xcf7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 40

    requires s0.stack[1] == 0xd34

    requires s0.stack[6] == 0xd57

    requires s0.stack[10] == 0x880

    requires s0.stack[13] == 0x831

    requires s0.stack[19] == 0x799

    requires s0.stack[26] == 0x588

    requires s0.stack[30] == 0x463

    requires s0.stack[34] == 0x22d

    requires s0.stack[38] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd34;
      assert s1.Peek(6) == 0xd57;
      assert s1.Peek(10) == 0x880;
      assert s1.Peek(13) == 0x831;
      assert s1.Peek(19) == 0x799;
      assert s1.Peek(26) == 0x588;
      assert s1.Peek(30) == 0x463;
      assert s1.Peek(34) == 0x22d;
      assert s1.Peek(38) == 0xa8;
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
      assert s11.Peek(0) == 0xd34;
      assert s11.Peek(7) == 0xd57;
      assert s11.Peek(11) == 0x880;
      assert s11.Peek(14) == 0x831;
      assert s11.Peek(20) == 0x799;
      assert s11.Peek(27) == 0x588;
      assert s11.Peek(31) == 0x463;
      assert s11.Peek(35) == 0x22d;
      assert s11.Peek(39) == 0xa8;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s14, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 228
    * Starting at 0xd34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[5] == 0xd57

    requires s0.stack[9] == 0x880

    requires s0.stack[12] == 0x831

    requires s0.stack[18] == 0x799

    requires s0.stack[25] == 0x588

    requires s0.stack[29] == 0x463

    requires s0.stack[33] == 0x22d

    requires s0.stack[37] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd57;
      assert s1.Peek(9) == 0x880;
      assert s1.Peek(12) == 0x831;
      assert s1.Peek(18) == 0x799;
      assert s1.Peek(25) == 0x588;
      assert s1.Peek(29) == 0x463;
      assert s1.Peek(33) == 0x22d;
      assert s1.Peek(37) == 0xa8;
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
      ExecuteFromCFGNode_s348(s11, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 230
    * Starting at 0xd57
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[4] == 0x880

    requires s0.stack[7] == 0x831

    requires s0.stack[13] == 0x799

    requires s0.stack[20] == 0x588

    requires s0.stack[24] == 0x463

    requires s0.stack[28] == 0x22d

    requires s0.stack[32] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x880;
      assert s1.Peek(7) == 0x831;
      assert s1.Peek(13) == 0x799;
      assert s1.Peek(20) == 0x588;
      assert s1.Peek(24) == 0x463;
      assert s1.Peek(28) == 0x22d;
      assert s1.Peek(32) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s349(s8, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 139
    * Starting at 0x880
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x880 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[3] == 0x831

    requires s0.stack[9] == 0x799

    requires s0.stack[16] == 0x588

    requires s0.stack[20] == 0x463

    requires s0.stack[24] == 0x22d

    requires s0.stack[28] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x831;
      assert s1.Peek(9) == 0x799;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x22d;
      assert s1.Peek(28) == 0xa8;
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

  /** Node 350
    * Segment Id for this node is: 121
    * Starting at 0x783
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x588

    requires s0.stack[13] == 0x463

    requires s0.stack[17] == 0x22d

    requires s0.stack[21] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x588;
      assert s1.Peek(13) == 0x463;
      assert s1.Peek(17) == 0x22d;
      assert s1.Peek(21) == 0xa8;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s306(s4, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 51
    * Starting at 0x232
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x232 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa8;
      var s2 := Push2(s1, 0x023a);
      var s3 := Push2(s2, 0x0126);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s4, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 35
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x23a

    requires s0.stack[4] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x23a;
      assert s1.Peek(4) == 0xa8;
      var s2 := Push2(s1, 0x012e);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s4, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 75
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x23a

    requires s0.stack[5] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x23a;
      assert s1.Peek(5) == 0xa8;
      var s2 := Push2(s1, 0x0348);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s4, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x348

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x23a

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x348;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x23a;
      assert s1.Peek(6) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s8, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x348

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x23a

    requires s0.stack[9] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x348;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x23a;
      assert s1.Peek(9) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s9, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x348

    requires s0.stack[3] == 0x12e

    requires s0.stack[4] == 0x23a

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(3) == 0x12e;
      assert s1.Peek(4) == 0x23a;
      assert s1.Peek(8) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x348;
      assert s11.Peek(3) == 0x12e;
      assert s11.Peek(4) == 0x23a;
      assert s11.Peek(8) == 0xa8;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s17, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 76
    * Starting at 0x348
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x23a

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x23a;
      assert s1.Peek(6) == 0xa8;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x03b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s367(s9, gas - 1)
      else
        ExecuteFromCFGNode_s358(s9, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 77
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x23a

    requires s0.stack[5] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x23a;
      assert s1.Peek(6) == 0xa8;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0aa2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s359(s11, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 187
    * Starting at 0xaa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x3ac

    requires s0.stack[2] == 0x12e

    requires s0.stack[3] == 0x23a

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ac;
      assert s1.Peek(2) == 0x12e;
      assert s1.Peek(3) == 0x23a;
      assert s1.Peek(7) == 0xa8;
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
      assert s11.Peek(4) == 0x3ac;
      assert s11.Peek(5) == 0x12e;
      assert s11.Peek(6) == 0x23a;
      assert s11.Peek(10) == 0xa8;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ab9);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0a80);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s18, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 184
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xab9

    requires s0.stack[4] == 0x3ac

    requires s0.stack[5] == 0x12e

    requires s0.stack[6] == 0x23a

    requires s0.stack[10] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab9;
      assert s1.Peek(4) == 0x3ac;
      assert s1.Peek(5) == 0x12e;
      assert s1.Peek(6) == 0x23a;
      assert s1.Peek(10) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0a8c);
      var s4 := Push1(s3, 0x42);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s361(s7, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xa8c

    requires s0.stack[5] == 0xab9

    requires s0.stack[8] == 0x3ac

    requires s0.stack[9] == 0x12e

    requires s0.stack[10] == 0x23a

    requires s0.stack[14] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8c;
      assert s1.Peek(5) == 0xab9;
      assert s1.Peek(8) == 0x3ac;
      assert s1.Peek(9) == 0x12e;
      assert s1.Peek(10) == 0x23a;
      assert s1.Peek(14) == 0xa8;
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
      assert s11.Peek(0) == 0xa8c;
      assert s11.Peek(6) == 0xab9;
      assert s11.Peek(9) == 0x3ac;
      assert s11.Peek(10) == 0x12e;
      assert s11.Peek(11) == 0x23a;
      assert s11.Peek(15) == 0xa8;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s15, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 185
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xab9

    requires s0.stack[6] == 0x3ac

    requires s0.stack[7] == 0x12e

    requires s0.stack[8] == 0x23a

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab9;
      assert s1.Peek(6) == 0x3ac;
      assert s1.Peek(7) == 0x12e;
      assert s1.Peek(8) == 0x23a;
      assert s1.Peek(12) == 0xa8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a97);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0a0c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s7, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 183
    * Starting at 0xa0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xa97

    requires s0.stack[4] == 0xab9

    requires s0.stack[7] == 0x3ac

    requires s0.stack[8] == 0x12e

    requires s0.stack[9] == 0x23a

    requires s0.stack[13] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa97;
      assert s1.Peek(4) == 0xab9;
      assert s1.Peek(7) == 0x3ac;
      assert s1.Peek(8) == 0x12e;
      assert s1.Peek(9) == 0x23a;
      assert s1.Peek(13) == 0xa8;
      var s2 := Push32(s1, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa97;
      assert s11.Peek(4) == 0xab9;
      assert s11.Peek(7) == 0x3ac;
      assert s11.Peek(8) == 0x12e;
      assert s11.Peek(9) == 0x23a;
      assert s11.Peek(13) == 0xa8;
      var s12 := Push32(s11, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s364(s18, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 186
    * Starting at 0xa97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xab9

    requires s0.stack[5] == 0x3ac

    requires s0.stack[6] == 0x12e

    requires s0.stack[7] == 0x23a

    requires s0.stack[11] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab9;
      assert s1.Peek(5) == 0x3ac;
      assert s1.Peek(6) == 0x12e;
      assert s1.Peek(7) == 0x23a;
      assert s1.Peek(11) == 0xa8;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s10, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 188
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3ac

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x23a

    requires s0.stack[9] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ac;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x23a;
      assert s1.Peek(9) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s366(s7, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 78
    * Starting at 0x3ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x23a

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x23a;
      assert s1.Peek(6) == 0xa8;
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

  /** Node 367
    * Segment Id for this node is: 79
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x23a

    requires s0.stack[5] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x23a;
      assert s1.Peek(5) == 0xa8;
      var s2 := Push2(s1, 0x03bd);
      var s3 := Push2(s2, 0x04b6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s4, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 99
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x3bd

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x23a

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bd;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x23a;
      assert s1.Peek(6) == 0xa8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s2, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 80
    * Starting at 0x3bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x23a

    requires s0.stack[5] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x23a;
      assert s1.Peek(5) == 0xa8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s2, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 36
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x23a

    requires s0.stack[4] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x23a;
      assert s1.Peek(4) == 0xa8;
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0139);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s371(s5, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x139

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x23a

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x23a;
      assert s1.Peek(6) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s5, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x23a

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x23a;
      assert s1.Peek(8) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s8, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x139

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x23a

    requires s0.stack[11] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x139;
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x23a;
      assert s1.Peek(11) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s9, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x139

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x23a

    requires s0.stack[10] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x139;
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x23a;
      assert s1.Peek(10) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x139;
      assert s11.Peek(5) == 0x13e;
      assert s11.Peek(6) == 0x23a;
      assert s11.Peek(10) == 0xa8;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s17, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x23a

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x23a;
      assert s1.Peek(8) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s376(s5, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 37
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x23a

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x23a;
      assert s1.Peek(6) == 0xa8;
      var s2 := Push2(s1, 0x03cd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s3, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 83
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x23a

    requires s0.stack[6] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x23a;
      assert s1.Peek(6) == 0xa8;
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
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x23a;
      assert s11.Peek(12) == 0xa8;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x03e8);
      assert s21.Peek(0) == 0x3e8;
      assert s21.Peek(5) == 0x13e;
      assert s21.Peek(6) == 0x23a;
      assert s21.Peek(10) == 0xa8;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s379(s22, gas - 1)
      else
        ExecuteFromCFGNode_s378(s22, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 84
    * Starting at 0x3e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x23a

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x13e;
      assert s1.Peek(5) == 0x23a;
      assert s1.Peek(9) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 379
    * Segment Id for this node is: 85
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x23a

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x23a;
      assert s1.Peek(8) == 0xa8;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 380
    * Segment Id for this node is: 12
    * Starting at 0x66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66 as nat
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
        ExecuteFromCFGNode_s382(s6, gas - 1)
      else
        ExecuteFromCFGNode_s381(s6, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 13
    * Starting at 0x6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 382
    * Segment Id for this node is: 14
    * Starting at 0x71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push2(s2, 0x008c);
      var s4 := Push1(s3, 0x04);
      var s5 := Dup1(s4);
      var s6 := CallDataSize(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x0087);
      assert s11.Peek(0) == 0x87;
      assert s11.Peek(3) == 0x8c;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x08eb);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s15, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 151
    * Starting at 0x8eb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x87

    requires s0.stack[3] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x87;
      assert s1.Peek(3) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0900);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s386(s10, gas - 1)
      else
        ExecuteFromCFGNode_s384(s10, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 152
    * Starting at 0x8f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x87

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x08ff);
      assert s1.Peek(0) == 0x8ff;
      assert s1.Peek(4) == 0x87;
      assert s1.Peek(5) == 0x8c;
      var s2 := Push2(s1, 0x0889);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s3, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 140
    * Starting at 0x889
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x889 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x8ff

    requires s0.stack[4] == 0x87

    requires s0.stack[5] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8ff;
      assert s1.Peek(4) == 0x87;
      assert s1.Peek(5) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 386
    * Segment Id for this node is: 154
    * Starting at 0x900
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x900 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x87

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x87;
      assert s1.Peek(4) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x090d);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x08d7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s9, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 149
    * Starting at 0x8d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x90d

    requires s0.stack[7] == 0x87

    requires s0.stack[8] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x90d;
      assert s1.Peek(7) == 0x87;
      assert s1.Peek(8) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x08e5);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x08c1);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s388(s10, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 145
    * Starting at 0x8c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x90d

    requires s0.stack[10] == 0x87

    requires s0.stack[11] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      assert s1.Peek(5) == 0x90d;
      assert s1.Peek(10) == 0x87;
      assert s1.Peek(11) == 0x8c;
      var s2 := Push2(s1, 0x08ca);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08b0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s389(s5, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 143
    * Starting at 0x8b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x8ca

    requires s0.stack[3] == 0x8e5

    requires s0.stack[7] == 0x90d

    requires s0.stack[12] == 0x87

    requires s0.stack[13] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ca;
      assert s1.Peek(3) == 0x8e5;
      assert s1.Peek(7) == 0x90d;
      assert s1.Peek(12) == 0x87;
      assert s1.Peek(13) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x08ba);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0891);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s6, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 142
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x8ba

    requires s0.stack[4] == 0x8ca

    requires s0.stack[6] == 0x8e5

    requires s0.stack[10] == 0x90d

    requires s0.stack[15] == 0x87

    requires s0.stack[16] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ba;
      assert s1.Peek(4) == 0x8ca;
      assert s1.Peek(6) == 0x8e5;
      assert s1.Peek(10) == 0x90d;
      assert s1.Peek(15) == 0x87;
      assert s1.Peek(16) == 0x8c;
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
      ExecuteFromCFGNode_s391(s11, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 144
    * Starting at 0x8ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x8ca

    requires s0.stack[5] == 0x8e5

    requires s0.stack[9] == 0x90d

    requires s0.stack[14] == 0x87

    requires s0.stack[15] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ca;
      assert s1.Peek(5) == 0x8e5;
      assert s1.Peek(9) == 0x90d;
      assert s1.Peek(14) == 0x87;
      assert s1.Peek(15) == 0x8c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s7, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 146
    * Starting at 0x8ca
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x8e5

    requires s0.stack[6] == 0x90d

    requires s0.stack[11] == 0x87

    requires s0.stack[12] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e5;
      assert s1.Peek(6) == 0x90d;
      assert s1.Peek(11) == 0x87;
      assert s1.Peek(12) == 0x8c;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x08d4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s394(s5, gas - 1)
      else
        ExecuteFromCFGNode_s393(s5, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 147
    * Starting at 0x8d1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x90d

    requires s0.stack[10] == 0x87

    requires s0.stack[11] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x8e5;
      assert s1.Peek(6) == 0x90d;
      assert s1.Peek(11) == 0x87;
      assert s1.Peek(12) == 0x8c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 394
    * Segment Id for this node is: 148
    * Starting at 0x8d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x8e5

    requires s0.stack[5] == 0x90d

    requires s0.stack[10] == 0x87

    requires s0.stack[11] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      assert s1.Peek(5) == 0x90d;
      assert s1.Peek(10) == 0x87;
      assert s1.Peek(11) == 0x8c;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s3, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 150
    * Starting at 0x8e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x90d

    requires s0.stack[8] == 0x87

    requires s0.stack[9] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x90d;
      assert s1.Peek(8) == 0x87;
      assert s1.Peek(9) == 0x8c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s6, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 155
    * Starting at 0x90d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x87

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x87;
      assert s1.Peek(6) == 0x8c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s9, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 15
    * Starting at 0x87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8c;
      var s2 := Push2(s1, 0x0140);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s3, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 39
    * Starting at 0x140
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8c;
      var s2 := Push2(s1, 0x0148);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s399(s4, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x148

    requires s0.stack[2] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x148;
      assert s1.Peek(2) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s400(s8, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x148

    requires s0.stack[5] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x148;
      assert s1.Peek(5) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s9, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x148

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x148;
      assert s1.Peek(4) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x148;
      assert s11.Peek(4) == 0x8c;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s402(s17, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 40
    * Starting at 0x148
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8c;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x0198);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s487(s9, gas - 1)
      else
        ExecuteFromCFGNode_s403(s9, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 41
    * Starting at 0x17b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0193);
      assert s1.Peek(0) == 0x193;
      assert s1.Peek(2) == 0x8c;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MStore(s8);
      var s10 := Dup1(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x193;
      assert s11.Peek(6) == 0x8c;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Pop(s13);
      var s15 := Push0(s14);
      var s16 := Push2(s15, 0x043f);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s17, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 88
    * Starting at 0x43f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x193

    requires s0.stack[5] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x193;
      assert s1.Peek(5) == 0x8c;
      var s2 := Push2(s1, 0x0448);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0514);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s5, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 103
    * Starting at 0x514
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x514 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x448

    requires s0.stack[5] == 0x193

    requires s0.stack[7] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x448;
      assert s1.Peek(5) == 0x193;
      assert s1.Peek(7) == 0x8c;
      var s2 := Push2(s1, 0x051d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x066c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s5, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 112
    * Starting at 0x66c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x51d

    requires s0.stack[3] == 0x448

    requires s0.stack[7] == 0x193

    requires s0.stack[9] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x51d;
      assert s1.Peek(3) == 0x448;
      assert s1.Peek(7) == 0x193;
      assert s1.Peek(9) == 0x8c;
      var s2 := Push2(s1, 0x0675);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x07a4);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s5, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 124
    * Starting at 0x7a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x675

    requires s0.stack[3] == 0x51d

    requires s0.stack[5] == 0x448

    requires s0.stack[9] == 0x193

    requires s0.stack[11] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x675;
      assert s1.Peek(3) == 0x51d;
      assert s1.Peek(5) == 0x448;
      assert s1.Peek(9) == 0x193;
      assert s1.Peek(11) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := ExtCodeSize(s6);
      var s8 := Gt(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x675;
      assert s11.Peek(4) == 0x51d;
      assert s11.Peek(6) == 0x448;
      assert s11.Peek(10) == 0x193;
      assert s11.Peek(12) == 0x8c;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s14, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 113
    * Starting at 0x675
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x675 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x51d

    requires s0.stack[4] == 0x448

    requires s0.stack[8] == 0x193

    requires s0.stack[10] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x51d;
      assert s1.Peek(4) == 0x448;
      assert s1.Peek(8) == 0x193;
      assert s1.Peek(10) == 0x8c;
      var s2 := Push2(s1, 0x06b4);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s418(s3, gas - 1)
      else
        ExecuteFromCFGNode_s409(s3, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 114
    * Starting at 0x67a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x51d

    requires s0.stack[3] == 0x448

    requires s0.stack[7] == 0x193

    requires s0.stack[9] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x51d;
      assert s1.Peek(4) == 0x448;
      assert s1.Peek(8) == 0x193;
      assert s1.Peek(10) == 0x8c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x06ab);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0be5);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s11, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 202
    * Starting at 0xbe5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x6ab

    requires s0.stack[3] == 0x51d

    requires s0.stack[5] == 0x448

    requires s0.stack[9] == 0x193

    requires s0.stack[11] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6ab;
      assert s1.Peek(3) == 0x51d;
      assert s1.Peek(5) == 0x448;
      assert s1.Peek(9) == 0x193;
      assert s1.Peek(11) == 0x8c;
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
      assert s11.Peek(4) == 0x6ab;
      assert s11.Peek(6) == 0x51d;
      assert s11.Peek(8) == 0x448;
      assert s11.Peek(12) == 0x193;
      assert s11.Peek(14) == 0x8c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0bfc);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0bc3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s18, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 199
    * Starting at 0xbc3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xbfc

    requires s0.stack[4] == 0x6ab

    requires s0.stack[6] == 0x51d

    requires s0.stack[8] == 0x448

    requires s0.stack[12] == 0x193

    requires s0.stack[14] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbfc;
      assert s1.Peek(4) == 0x6ab;
      assert s1.Peek(6) == 0x51d;
      assert s1.Peek(8) == 0x448;
      assert s1.Peek(12) == 0x193;
      assert s1.Peek(14) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0bcf);
      var s4 := Push1(s3, 0x2d);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s7, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xbcf

    requires s0.stack[5] == 0xbfc

    requires s0.stack[8] == 0x6ab

    requires s0.stack[10] == 0x51d

    requires s0.stack[12] == 0x448

    requires s0.stack[16] == 0x193

    requires s0.stack[18] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbcf;
      assert s1.Peek(5) == 0xbfc;
      assert s1.Peek(8) == 0x6ab;
      assert s1.Peek(10) == 0x51d;
      assert s1.Peek(12) == 0x448;
      assert s1.Peek(16) == 0x193;
      assert s1.Peek(18) == 0x8c;
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
      assert s11.Peek(0) == 0xbcf;
      assert s11.Peek(6) == 0xbfc;
      assert s11.Peek(9) == 0x6ab;
      assert s11.Peek(11) == 0x51d;
      assert s11.Peek(13) == 0x448;
      assert s11.Peek(17) == 0x193;
      assert s11.Peek(19) == 0x8c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s15, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 200
    * Starting at 0xbcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xbfc

    requires s0.stack[6] == 0x6ab

    requires s0.stack[8] == 0x51d

    requires s0.stack[10] == 0x448

    requires s0.stack[14] == 0x193

    requires s0.stack[16] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbfc;
      assert s1.Peek(6) == 0x6ab;
      assert s1.Peek(8) == 0x51d;
      assert s1.Peek(10) == 0x448;
      assert s1.Peek(14) == 0x193;
      assert s1.Peek(16) == 0x8c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0bda);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0b75);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s7, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 198
    * Starting at 0xb75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xbda

    requires s0.stack[4] == 0xbfc

    requires s0.stack[7] == 0x6ab

    requires s0.stack[9] == 0x51d

    requires s0.stack[11] == 0x448

    requires s0.stack[15] == 0x193

    requires s0.stack[17] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbda;
      assert s1.Peek(4) == 0xbfc;
      assert s1.Peek(7) == 0x6ab;
      assert s1.Peek(9) == 0x51d;
      assert s1.Peek(11) == 0x448;
      assert s1.Peek(15) == 0x193;
      assert s1.Peek(17) == 0x8c;
      var s2 := Push32(s1, 0x455243313936373a206e657720696d706c656d656e746174696f6e206973206e);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6f74206120636f6e747261637400000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xbda;
      assert s11.Peek(4) == 0xbfc;
      assert s11.Peek(7) == 0x6ab;
      assert s11.Peek(9) == 0x51d;
      assert s11.Peek(11) == 0x448;
      assert s11.Peek(15) == 0x193;
      assert s11.Peek(17) == 0x8c;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s13, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 201
    * Starting at 0xbda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xbfc

    requires s0.stack[5] == 0x6ab

    requires s0.stack[7] == 0x51d

    requires s0.stack[9] == 0x448

    requires s0.stack[13] == 0x193

    requires s0.stack[15] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbfc;
      assert s1.Peek(5) == 0x6ab;
      assert s1.Peek(7) == 0x51d;
      assert s1.Peek(9) == 0x448;
      assert s1.Peek(13) == 0x193;
      assert s1.Peek(15) == 0x8c;
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
      ExecuteFromCFGNode_s416(s10, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 203
    * Starting at 0xbfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x6ab

    requires s0.stack[5] == 0x51d

    requires s0.stack[7] == 0x448

    requires s0.stack[11] == 0x193

    requires s0.stack[13] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6ab;
      assert s1.Peek(5) == 0x51d;
      assert s1.Peek(7) == 0x448;
      assert s1.Peek(11) == 0x193;
      assert s1.Peek(13) == 0x8c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s7, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 115
    * Starting at 0x6ab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x51d

    requires s0.stack[4] == 0x448

    requires s0.stack[8] == 0x193

    requires s0.stack[10] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x51d;
      assert s1.Peek(4) == 0x448;
      assert s1.Peek(8) == 0x193;
      assert s1.Peek(10) == 0x8c;
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

  /** Node 418
    * Segment Id for this node is: 116
    * Starting at 0x6b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x51d

    requires s0.stack[3] == 0x448

    requires s0.stack[7] == 0x193

    requires s0.stack[9] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x51d;
      assert s1.Peek(3) == 0x448;
      assert s1.Peek(7) == 0x193;
      assert s1.Peek(9) == 0x8c;
      var s2 := Dup1(s1);
      var s3 := Push2(s2, 0x06e0);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s419(s8, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x6e0

    requires s0.stack[4] == 0x51d

    requires s0.stack[6] == 0x448

    requires s0.stack[10] == 0x193

    requires s0.stack[12] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6e0;
      assert s1.Peek(4) == 0x51d;
      assert s1.Peek(6) == 0x448;
      assert s1.Peek(10) == 0x193;
      assert s1.Peek(12) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s9, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 117
    * Starting at 0x6e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x51d

    requires s0.stack[5] == 0x448

    requires s0.stack[9] == 0x193

    requires s0.stack[11] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x51d;
      assert s1.Peek(5) == 0x448;
      assert s1.Peek(9) == 0x193;
      assert s1.Peek(11) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Push2(s4, 0x0100);
      var s6 := Exp(s5);
      var s7 := Dup2(s6);
      var s8 := SLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := Mul(s10);
      assert s11.Peek(6) == 0x51d;
      assert s11.Peek(8) == 0x448;
      assert s11.Peek(12) == 0x193;
      assert s11.Peek(14) == 0x8c;
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
      assert s21.Peek(2) == 0x51d;
      assert s21.Peek(4) == 0x448;
      assert s21.Peek(8) == 0x193;
      assert s21.Peek(10) == 0x8c;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s24, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 104
    * Starting at 0x51d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x448

    requires s0.stack[5] == 0x193

    requires s0.stack[7] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x448;
      assert s1.Peek(5) == 0x193;
      assert s1.Peek(7) == 0x8c;
      var s2 := Dup1(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push32(s4, 0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Dup1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0x448;
      assert s11.Peek(10) == 0x193;
      assert s11.Peek(12) == 0x8c;
      var s12 := Sub(s11);
      var s13 := Swap1(s12);
      var s14 := Log2(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s422(s16, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 89
    * Starting at 0x448
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x448 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x193

    requires s0.stack[5] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x193;
      assert s1.Peek(5) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Gt(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x0454);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s424(s8, gas - 1)
      else
        ExecuteFromCFGNode_s423(s8, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 90
    * Starting at 0x452
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x452 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x193

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x193;
      assert s1.Peek(5) == 0x8c;
      var s2 := Dup1(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s424(s2, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 91
    * Starting at 0x454
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x454 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x193

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x193;
      assert s1.Peek(6) == 0x8c;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0465);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s463(s4, gas - 1)
      else
        ExecuteFromCFGNode_s425(s4, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 92
    * Starting at 0x45a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x193

    requires s0.stack[5] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0463);
      assert s1.Peek(0) == 0x463;
      assert s1.Peek(4) == 0x193;
      assert s1.Peek(6) == 0x8c;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0563);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s426(s5, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 105
    * Starting at 0x563
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x563 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x463

    requires s0.stack[6] == 0x193

    requires s0.stack[8] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x463;
      assert s1.Peek(6) == 0x193;
      assert s1.Peek(8) == 0x8c;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0588);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x588;
      assert s11.Peek(9) == 0x463;
      assert s11.Peek(13) == 0x193;
      assert s11.Peek(15) == 0x8c;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x27);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0d60);
      var s20 := Push1(s19, 0x27);
      var s21 := Swap2(s20);
      assert s21.Peek(6) == 0x588;
      assert s21.Peek(10) == 0x463;
      assert s21.Peek(14) == 0x193;
      assert s21.Peek(16) == 0x8c;
      var s22 := CodeCopy(s21);
      var s23 := Push2(s22, 0x0722);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s427(s24, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 118
    * Starting at 0x722
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x722 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x588

    requires s0.stack[7] == 0x463

    requires s0.stack[11] == 0x193

    requires s0.stack[13] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x588;
      assert s1.Peek(7) == 0x463;
      assert s1.Peek(11) == 0x193;
      assert s1.Peek(13) == 0x8c;
      var s2 := Push1(s1, 0x60);
      var s3 := Push0(s2);
      var s4 := Dup1(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Dup6(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x074b);
      assert s11.Peek(0) == 0x74b;
      assert s11.Peek(10) == 0x588;
      assert s11.Peek(14) == 0x463;
      assert s11.Peek(18) == 0x193;
      assert s11.Peek(20) == 0x8c;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0c6f);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s428(s15, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 214
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x74b

    requires s0.stack[10] == 0x588

    requires s0.stack[14] == 0x463

    requires s0.stack[18] == 0x193

    requires s0.stack[20] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x74b;
      assert s1.Peek(10) == 0x588;
      assert s1.Peek(14) == 0x463;
      assert s1.Peek(18) == 0x193;
      assert s1.Peek(20) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c7a);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0c3f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s429(s7, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 210
    * Starting at 0xc3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0xc7a

    requires s0.stack[6] == 0x74b

    requires s0.stack[14] == 0x588

    requires s0.stack[18] == 0x463

    requires s0.stack[22] == 0x193

    requires s0.stack[24] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc7a;
      assert s1.Peek(6) == 0x74b;
      assert s1.Peek(14) == 0x588;
      assert s1.Peek(18) == 0x463;
      assert s1.Peek(22) == 0x193;
      assert s1.Peek(24) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c49);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c03);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s6, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 204
    * Starting at 0xc03
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xc49

    requires s0.stack[5] == 0xc7a

    requires s0.stack[9] == 0x74b

    requires s0.stack[17] == 0x588

    requires s0.stack[21] == 0x463

    requires s0.stack[25] == 0x193

    requires s0.stack[27] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc49;
      assert s1.Peek(5) == 0xc7a;
      assert s1.Peek(9) == 0x74b;
      assert s1.Peek(17) == 0x588;
      assert s1.Peek(21) == 0x463;
      assert s1.Peek(25) == 0x193;
      assert s1.Peek(27) == 0x8c;
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
      ExecuteFromCFGNode_s431(s10, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 211
    * Starting at 0xc49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xc7a

    requires s0.stack[8] == 0x74b

    requires s0.stack[16] == 0x588

    requires s0.stack[20] == 0x463

    requires s0.stack[24] == 0x193

    requires s0.stack[26] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc7a;
      assert s1.Peek(8) == 0x74b;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x193;
      assert s1.Peek(26) == 0x8c;
      var s2 := Push2(s1, 0x0c53);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0c0d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s6, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 205
    * Starting at 0xc0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[2] == 0xc53

    requires s0.stack[7] == 0xc7a

    requires s0.stack[11] == 0x74b

    requires s0.stack[19] == 0x588

    requires s0.stack[23] == 0x463

    requires s0.stack[27] == 0x193

    requires s0.stack[29] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc53;
      assert s1.Peek(7) == 0xc7a;
      assert s1.Peek(11) == 0x74b;
      assert s1.Peek(19) == 0x588;
      assert s1.Peek(23) == 0x463;
      assert s1.Peek(27) == 0x193;
      assert s1.Peek(29) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s433(s10, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 212
    * Starting at 0xc53
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xc7a

    requires s0.stack[9] == 0x74b

    requires s0.stack[17] == 0x588

    requires s0.stack[21] == 0x463

    requires s0.stack[25] == 0x193

    requires s0.stack[27] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc7a;
      assert s1.Peek(9) == 0x74b;
      assert s1.Peek(17) == 0x588;
      assert s1.Peek(21) == 0x463;
      assert s1.Peek(25) == 0x193;
      assert s1.Peek(27) == 0x8c;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0c63);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0c17);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s11, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 206
    * Starting at 0xc17
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[3] == 0xc63

    requires s0.stack[8] == 0xc7a

    requires s0.stack[12] == 0x74b

    requires s0.stack[20] == 0x588

    requires s0.stack[24] == 0x463

    requires s0.stack[28] == 0x193

    requires s0.stack[30] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc63;
      assert s1.Peek(8) == 0xc7a;
      assert s1.Peek(12) == 0x74b;
      assert s1.Peek(20) == 0x588;
      assert s1.Peek(24) == 0x463;
      assert s1.Peek(28) == 0x193;
      assert s1.Peek(30) == 0x8c;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s435(s2, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 207
    * Starting at 0xc19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[4] == 0xc63

    requires s0.stack[9] == 0xc7a

    requires s0.stack[13] == 0x74b

    requires s0.stack[21] == 0x588

    requires s0.stack[25] == 0x463

    requires s0.stack[29] == 0x193

    requires s0.stack[31] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc63;
      assert s1.Peek(9) == 0xc7a;
      assert s1.Peek(13) == 0x74b;
      assert s1.Peek(21) == 0x588;
      assert s1.Peek(25) == 0x463;
      assert s1.Peek(29) == 0x193;
      assert s1.Peek(31) == 0x8c;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c34);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s437(s7, gas - 1)
      else
        ExecuteFromCFGNode_s436(s7, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 208
    * Starting at 0xc22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[4] == 0xc63

    requires s0.stack[9] == 0xc7a

    requires s0.stack[13] == 0x74b

    requires s0.stack[21] == 0x588

    requires s0.stack[25] == 0x463

    requires s0.stack[29] == 0x193

    requires s0.stack[31] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xc63;
      assert s1.Peek(10) == 0xc7a;
      assert s1.Peek(14) == 0x74b;
      assert s1.Peek(22) == 0x588;
      assert s1.Peek(26) == 0x463;
      assert s1.Peek(30) == 0x193;
      assert s1.Peek(32) == 0x8c;
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
      assert s11.Peek(5) == 0xc63;
      assert s11.Peek(10) == 0xc7a;
      assert s11.Peek(14) == 0x74b;
      assert s11.Peek(22) == 0x588;
      assert s11.Peek(26) == 0x463;
      assert s11.Peek(30) == 0x193;
      assert s11.Peek(32) == 0x8c;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0c19);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s15, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 209
    * Starting at 0xc34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[4] == 0xc63

    requires s0.stack[9] == 0xc7a

    requires s0.stack[13] == 0x74b

    requires s0.stack[21] == 0x588

    requires s0.stack[25] == 0x463

    requires s0.stack[29] == 0x193

    requires s0.stack[31] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc63;
      assert s1.Peek(9) == 0xc7a;
      assert s1.Peek(13) == 0x74b;
      assert s1.Peek(21) == 0x588;
      assert s1.Peek(25) == 0x463;
      assert s1.Peek(29) == 0x193;
      assert s1.Peek(31) == 0x8c;
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
      ExecuteFromCFGNode_s438(s11, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 213
    * Starting at 0xc63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xc7a

    requires s0.stack[8] == 0x74b

    requires s0.stack[16] == 0x588

    requires s0.stack[20] == 0x463

    requires s0.stack[24] == 0x193

    requires s0.stack[26] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc7a;
      assert s1.Peek(8) == 0x74b;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x193;
      assert s1.Peek(26) == 0x8c;
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Swap3(s7);
      var s9 := Swap2(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0xc7a;
      assert s11.Peek(5) == 0x74b;
      assert s11.Peek(13) == 0x588;
      assert s11.Peek(17) == 0x463;
      assert s11.Peek(21) == 0x193;
      assert s11.Peek(23) == 0x8c;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s12, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 215
    * Starting at 0xc7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0x74b

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x193

    requires s0.stack[22] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x74b;
      assert s1.Peek(12) == 0x588;
      assert s1.Peek(16) == 0x463;
      assert s1.Peek(20) == 0x193;
      assert s1.Peek(22) == 0x8c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s440(s11, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 119
    * Starting at 0x74b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x588

    requires s0.stack[12] == 0x463

    requires s0.stack[16] == 0x193

    requires s0.stack[18] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x588;
      assert s1.Peek(12) == 0x463;
      assert s1.Peek(16) == 0x193;
      assert s1.Peek(18) == 0x8c;
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
      assert s11.Peek(9) == 0x588;
      assert s11.Peek(13) == 0x463;
      assert s11.Peek(17) == 0x193;
      assert s11.Peek(19) == 0x8c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup1(s15);
      var s17 := Push0(s16);
      var s18 := Dup2(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x0783);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s486(s21, gas - 1)
      else
        ExecuteFromCFGNode_s441(s21, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 120
    * Starting at 0x763
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x763 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[9] == 0x588

    requires s0.stack[13] == 0x463

    requires s0.stack[17] == 0x193

    requires s0.stack[19] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0x588;
      assert s1.Peek(14) == 0x463;
      assert s1.Peek(18) == 0x193;
      assert s1.Peek(20) == 0x8c;
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
      assert s11.Peek(11) == 0x588;
      assert s11.Peek(15) == 0x463;
      assert s11.Peek(19) == 0x193;
      assert s11.Peek(21) == 0x8c;
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
      assert s21.Peek(13) == 0x588;
      assert s21.Peek(17) == 0x463;
      assert s21.Peek(21) == 0x193;
      assert s21.Peek(23) == 0x8c;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0788);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s25, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 122
    * Starting at 0x788
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x788 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[9] == 0x588

    requires s0.stack[13] == 0x463

    requires s0.stack[17] == 0x193

    requires s0.stack[19] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x588;
      assert s1.Peek(13) == 0x463;
      assert s1.Peek(17) == 0x193;
      assert s1.Peek(19) == 0x8c;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0799);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Dup4(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(4) == 0x799;
      assert s11.Peek(11) == 0x588;
      assert s11.Peek(15) == 0x463;
      assert s11.Peek(19) == 0x193;
      assert s11.Peek(21) == 0x8c;
      var s12 := Push2(s11, 0x07c6);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s13, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 125
    * Starting at 0x7c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0x799

    requires s0.stack[11] == 0x588

    requires s0.stack[15] == 0x463

    requires s0.stack[19] == 0x193

    requires s0.stack[21] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x799;
      assert s1.Peek(11) == 0x588;
      assert s1.Peek(15) == 0x463;
      assert s1.Peek(19) == 0x193;
      assert s1.Peek(21) == 0x8c;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0827);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s467(s6, gas - 1)
      else
        ExecuteFromCFGNode_s444(s6, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 126
    * Starting at 0x7cf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x193

    requires s0.stack[22] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x193;
      assert s1.Peek(23) == 0x8c;
      var s2 := Dup4(s1);
      var s3 := MLoad(s2);
      var s4 := Sub(s3);
      var s5 := Push2(s4, 0x081f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s458(s6, gas - 1)
      else
        ExecuteFromCFGNode_s445(s6, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 127
    * Starting at 0x7d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x193

    requires s0.stack[22] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x07df);
      assert s1.Peek(0) == 0x7df;
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x193;
      assert s1.Peek(23) == 0x8c;
      var s2 := Dup6(s1);
      var s3 := Push2(s2, 0x07a4);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s4, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 124
    * Starting at 0x7a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x7df

    requires s0.stack[7] == 0x799

    requires s0.stack[14] == 0x588

    requires s0.stack[18] == 0x463

    requires s0.stack[22] == 0x193

    requires s0.stack[24] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7df;
      assert s1.Peek(7) == 0x799;
      assert s1.Peek(14) == 0x588;
      assert s1.Peek(18) == 0x463;
      assert s1.Peek(22) == 0x193;
      assert s1.Peek(24) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := ExtCodeSize(s6);
      var s8 := Gt(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x7df;
      assert s11.Peek(8) == 0x799;
      assert s11.Peek(15) == 0x588;
      assert s11.Peek(19) == 0x463;
      assert s11.Peek(23) == 0x193;
      assert s11.Peek(25) == 0x8c;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s447(s14, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 128
    * Starting at 0x7df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[6] == 0x799

    requires s0.stack[13] == 0x588

    requires s0.stack[17] == 0x463

    requires s0.stack[21] == 0x193

    requires s0.stack[23] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x193;
      assert s1.Peek(23) == 0x8c;
      var s2 := Push2(s1, 0x081e);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s457(s3, gas - 1)
      else
        ExecuteFromCFGNode_s448(s3, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 129
    * Starting at 0x7e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x193

    requires s0.stack[22] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x193;
      assert s1.Peek(23) == 0x8c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0815);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0ccf);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s449(s11, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 220
    * Starting at 0xccf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x815

    requires s0.stack[7] == 0x799

    requires s0.stack[14] == 0x588

    requires s0.stack[18] == 0x463

    requires s0.stack[22] == 0x193

    requires s0.stack[24] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x815;
      assert s1.Peek(7) == 0x799;
      assert s1.Peek(14) == 0x588;
      assert s1.Peek(18) == 0x463;
      assert s1.Peek(22) == 0x193;
      assert s1.Peek(24) == 0x8c;
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
      assert s11.Peek(4) == 0x815;
      assert s11.Peek(10) == 0x799;
      assert s11.Peek(17) == 0x588;
      assert s11.Peek(21) == 0x463;
      assert s11.Peek(25) == 0x193;
      assert s11.Peek(27) == 0x8c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ce6);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0cad);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s18, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 217
    * Starting at 0xcad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xce6

    requires s0.stack[4] == 0x815

    requires s0.stack[10] == 0x799

    requires s0.stack[17] == 0x588

    requires s0.stack[21] == 0x463

    requires s0.stack[25] == 0x193

    requires s0.stack[27] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xce6;
      assert s1.Peek(4) == 0x815;
      assert s1.Peek(10) == 0x799;
      assert s1.Peek(17) == 0x588;
      assert s1.Peek(21) == 0x463;
      assert s1.Peek(25) == 0x193;
      assert s1.Peek(27) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0cb9);
      var s4 := Push1(s3, 0x1d);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s7, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[2] == 0xcb9

    requires s0.stack[5] == 0xce6

    requires s0.stack[8] == 0x815

    requires s0.stack[14] == 0x799

    requires s0.stack[21] == 0x588

    requires s0.stack[25] == 0x463

    requires s0.stack[29] == 0x193

    requires s0.stack[31] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcb9;
      assert s1.Peek(5) == 0xce6;
      assert s1.Peek(8) == 0x815;
      assert s1.Peek(14) == 0x799;
      assert s1.Peek(21) == 0x588;
      assert s1.Peek(25) == 0x463;
      assert s1.Peek(29) == 0x193;
      assert s1.Peek(31) == 0x8c;
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
      assert s11.Peek(0) == 0xcb9;
      assert s11.Peek(6) == 0xce6;
      assert s11.Peek(9) == 0x815;
      assert s11.Peek(15) == 0x799;
      assert s11.Peek(22) == 0x588;
      assert s11.Peek(26) == 0x463;
      assert s11.Peek(30) == 0x193;
      assert s11.Peek(32) == 0x8c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s15, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 218
    * Starting at 0xcb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0xce6

    requires s0.stack[6] == 0x815

    requires s0.stack[12] == 0x799

    requires s0.stack[19] == 0x588

    requires s0.stack[23] == 0x463

    requires s0.stack[27] == 0x193

    requires s0.stack[29] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xce6;
      assert s1.Peek(6) == 0x815;
      assert s1.Peek(12) == 0x799;
      assert s1.Peek(19) == 0x588;
      assert s1.Peek(23) == 0x463;
      assert s1.Peek(27) == 0x193;
      assert s1.Peek(29) == 0x8c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0cc4);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0c85);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s7, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 216
    * Starting at 0xc85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[1] == 0xcc4

    requires s0.stack[4] == 0xce6

    requires s0.stack[7] == 0x815

    requires s0.stack[13] == 0x799

    requires s0.stack[20] == 0x588

    requires s0.stack[24] == 0x463

    requires s0.stack[28] == 0x193

    requires s0.stack[30] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcc4;
      assert s1.Peek(4) == 0xce6;
      assert s1.Peek(7) == 0x815;
      assert s1.Peek(13) == 0x799;
      assert s1.Peek(20) == 0x588;
      assert s1.Peek(24) == 0x463;
      assert s1.Peek(28) == 0x193;
      assert s1.Peek(30) == 0x8c;
      var s2 := Push32(s1, 0x416464726573733a2063616c6c20746f206e6f6e2d636f6e7472616374000000);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s8, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 219
    * Starting at 0xcc4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0xce6

    requires s0.stack[5] == 0x815

    requires s0.stack[11] == 0x799

    requires s0.stack[18] == 0x588

    requires s0.stack[22] == 0x463

    requires s0.stack[26] == 0x193

    requires s0.stack[28] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xce6;
      assert s1.Peek(5) == 0x815;
      assert s1.Peek(11) == 0x799;
      assert s1.Peek(18) == 0x588;
      assert s1.Peek(22) == 0x463;
      assert s1.Peek(26) == 0x193;
      assert s1.Peek(28) == 0x8c;
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
      ExecuteFromCFGNode_s455(s10, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 221
    * Starting at 0xce6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x815

    requires s0.stack[9] == 0x799

    requires s0.stack[16] == 0x588

    requires s0.stack[20] == 0x463

    requires s0.stack[24] == 0x193

    requires s0.stack[26] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x815;
      assert s1.Peek(9) == 0x799;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x193;
      assert s1.Peek(26) == 0x8c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s7, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 130
    * Starting at 0x815
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x815 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[6] == 0x799

    requires s0.stack[13] == 0x588

    requires s0.stack[17] == 0x463

    requires s0.stack[21] == 0x193

    requires s0.stack[23] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x799;
      assert s1.Peek(13) == 0x588;
      assert s1.Peek(17) == 0x463;
      assert s1.Peek(21) == 0x193;
      assert s1.Peek(23) == 0x8c;
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

  /** Node 457
    * Segment Id for this node is: 131
    * Starting at 0x81e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x193

    requires s0.stack[22] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s458(s1, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 132
    * Starting at 0x81f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x193

    requires s0.stack[22] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x799;
      assert s1.Peek(12) == 0x588;
      assert s1.Peek(16) == 0x463;
      assert s1.Peek(20) == 0x193;
      assert s1.Peek(22) == 0x8c;
      var s2 := Dup3(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x0832);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s6, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 135
    * Starting at 0x832
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x832 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x193

    requires s0.stack[22] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x799;
      assert s1.Peek(12) == 0x588;
      assert s1.Peek(16) == 0x463;
      assert s1.Peek(20) == 0x193;
      assert s1.Peek(22) == 0x8c;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s8, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 123
    * Starting at 0x799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x588

    requires s0.stack[11] == 0x463

    requires s0.stack[15] == 0x193

    requires s0.stack[17] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x588;
      assert s1.Peek(11) == 0x463;
      assert s1.Peek(15) == 0x193;
      assert s1.Peek(17) == 0x8c;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap4(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s11, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 106
    * Starting at 0x588
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x588 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x463

    requires s0.stack[8] == 0x193

    requires s0.stack[10] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x463;
      assert s1.Peek(8) == 0x193;
      assert s1.Peek(10) == 0x8c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s8, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 93
    * Starting at 0x463
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x193

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x193;
      assert s1.Peek(6) == 0x8c;
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s463(s2, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 94
    * Starting at 0x465
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x465 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x193

    requires s0.stack[5] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x193;
      assert s1.Peek(5) == 0x8c;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s5, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 42
    * Starting at 0x193
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8c;
      var s2 := Push2(s1, 0x01a1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s3, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 45
    * Starting at 0x1a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8c;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s466(s3, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 16
    * Starting at 0x8c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c as nat
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

  /** Node 467
    * Segment Id for this node is: 133
    * Starting at 0x827
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x827 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x799

    requires s0.stack[12] == 0x588

    requires s0.stack[16] == 0x463

    requires s0.stack[20] == 0x193

    requires s0.stack[22] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x799;
      assert s1.Peek(12) == 0x588;
      assert s1.Peek(16) == 0x463;
      assert s1.Peek(20) == 0x193;
      assert s1.Peek(22) == 0x8c;
      var s2 := Push2(s1, 0x0831);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x083a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s468(s6, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 136
    * Starting at 0x83a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0x831

    requires s0.stack[8] == 0x799

    requires s0.stack[15] == 0x588

    requires s0.stack[19] == 0x463

    requires s0.stack[23] == 0x193

    requires s0.stack[25] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x831;
      assert s1.Peek(8) == 0x799;
      assert s1.Peek(15) == 0x588;
      assert s1.Peek(19) == 0x463;
      assert s1.Peek(23) == 0x193;
      assert s1.Peek(25) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x084c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s470(s8, gas - 1)
      else
        ExecuteFromCFGNode_s469(s8, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 137
    * Starting at 0x844
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x844 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0x831

    requires s0.stack[8] == 0x799

    requires s0.stack[15] == 0x588

    requires s0.stack[19] == 0x463

    requires s0.stack[23] == 0x193

    requires s0.stack[25] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(3) == 0x831;
      assert s1.Peek(9) == 0x799;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x193;
      assert s1.Peek(26) == 0x8c;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 470
    * Segment Id for this node is: 138
    * Starting at 0x84c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0x831

    requires s0.stack[8] == 0x799

    requires s0.stack[15] == 0x588

    requires s0.stack[19] == 0x463

    requires s0.stack[23] == 0x193

    requires s0.stack[25] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x831;
      assert s1.Peek(8) == 0x799;
      assert s1.Peek(15) == 0x588;
      assert s1.Peek(19) == 0x463;
      assert s1.Peek(23) == 0x193;
      assert s1.Peek(25) == 0x8c;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0880);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x880;
      assert s11.Peek(5) == 0x831;
      assert s11.Peek(11) == 0x799;
      assert s11.Peek(18) == 0x588;
      assert s11.Peek(22) == 0x463;
      assert s11.Peek(26) == 0x193;
      assert s11.Peek(28) == 0x8c;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d3f);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s14, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 229
    * Starting at 0xd3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0x880

    requires s0.stack[5] == 0x831

    requires s0.stack[11] == 0x799

    requires s0.stack[18] == 0x588

    requires s0.stack[22] == 0x463

    requires s0.stack[26] == 0x193

    requires s0.stack[28] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x880;
      assert s1.Peek(5) == 0x831;
      assert s1.Peek(11) == 0x799;
      assert s1.Peek(18) == 0x588;
      assert s1.Peek(22) == 0x463;
      assert s1.Peek(26) == 0x193;
      assert s1.Peek(28) == 0x8c;
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
      assert s11.Peek(5) == 0x880;
      assert s11.Peek(8) == 0x831;
      assert s11.Peek(14) == 0x799;
      assert s11.Peek(21) == 0x588;
      assert s11.Peek(25) == 0x463;
      assert s11.Peek(29) == 0x193;
      assert s11.Peek(31) == 0x8c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0d57);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0d07);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s19, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 224
    * Starting at 0xd07
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd07 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[2] == 0xd57

    requires s0.stack[6] == 0x880

    requires s0.stack[9] == 0x831

    requires s0.stack[15] == 0x799

    requires s0.stack[22] == 0x588

    requires s0.stack[26] == 0x463

    requires s0.stack[30] == 0x193

    requires s0.stack[32] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd57;
      assert s1.Peek(6) == 0x880;
      assert s1.Peek(9) == 0x831;
      assert s1.Peek(15) == 0x799;
      assert s1.Peek(22) == 0x588;
      assert s1.Peek(26) == 0x463;
      assert s1.Peek(30) == 0x193;
      assert s1.Peek(32) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d11);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0ced);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s6, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 222
    * Starting at 0xced
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xced as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[1] == 0xd11

    requires s0.stack[5] == 0xd57

    requires s0.stack[9] == 0x880

    requires s0.stack[12] == 0x831

    requires s0.stack[18] == 0x799

    requires s0.stack[25] == 0x588

    requires s0.stack[29] == 0x463

    requires s0.stack[33] == 0x193

    requires s0.stack[35] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd11;
      assert s1.Peek(5) == 0xd57;
      assert s1.Peek(9) == 0x880;
      assert s1.Peek(12) == 0x831;
      assert s1.Peek(18) == 0x799;
      assert s1.Peek(25) == 0x588;
      assert s1.Peek(29) == 0x463;
      assert s1.Peek(33) == 0x193;
      assert s1.Peek(35) == 0x8c;
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
      ExecuteFromCFGNode_s474(s10, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 225
    * Starting at 0xd11
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 36

    requires s0.stack[4] == 0xd57

    requires s0.stack[8] == 0x880

    requires s0.stack[11] == 0x831

    requires s0.stack[17] == 0x799

    requires s0.stack[24] == 0x588

    requires s0.stack[28] == 0x463

    requires s0.stack[32] == 0x193

    requires s0.stack[34] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd57;
      assert s1.Peek(8) == 0x880;
      assert s1.Peek(11) == 0x831;
      assert s1.Peek(17) == 0x799;
      assert s1.Peek(24) == 0x588;
      assert s1.Peek(28) == 0x463;
      assert s1.Peek(32) == 0x193;
      assert s1.Peek(34) == 0x8c;
      var s2 := Push2(s1, 0x0d1b);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x09fc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s475(s6, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[2] == 0xd1b

    requires s0.stack[7] == 0xd57

    requires s0.stack[11] == 0x880

    requires s0.stack[14] == 0x831

    requires s0.stack[20] == 0x799

    requires s0.stack[27] == 0x588

    requires s0.stack[31] == 0x463

    requires s0.stack[35] == 0x193

    requires s0.stack[37] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1b;
      assert s1.Peek(7) == 0xd57;
      assert s1.Peek(11) == 0x880;
      assert s1.Peek(14) == 0x831;
      assert s1.Peek(20) == 0x799;
      assert s1.Peek(27) == 0x588;
      assert s1.Peek(31) == 0x463;
      assert s1.Peek(35) == 0x193;
      assert s1.Peek(37) == 0x8c;
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
      assert s11.Peek(0) == 0xd1b;
      assert s11.Peek(8) == 0xd57;
      assert s11.Peek(12) == 0x880;
      assert s11.Peek(15) == 0x831;
      assert s11.Peek(21) == 0x799;
      assert s11.Peek(28) == 0x588;
      assert s11.Peek(32) == 0x463;
      assert s11.Peek(36) == 0x193;
      assert s11.Peek(38) == 0x8c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s15, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 226
    * Starting at 0xd1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[5] == 0xd57

    requires s0.stack[9] == 0x880

    requires s0.stack[12] == 0x831

    requires s0.stack[18] == 0x799

    requires s0.stack[25] == 0x588

    requires s0.stack[29] == 0x463

    requires s0.stack[33] == 0x193

    requires s0.stack[35] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd57;
      assert s1.Peek(9) == 0x880;
      assert s1.Peek(12) == 0x831;
      assert s1.Peek(18) == 0x799;
      assert s1.Peek(25) == 0x588;
      assert s1.Peek(29) == 0x463;
      assert s1.Peek(33) == 0x193;
      assert s1.Peek(35) == 0x8c;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0d2b);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0c17);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s477(s11, gas - 1)
  }

  /** Node 477
    * Segment Id for this node is: 206
    * Starting at 0xc17
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 40

    requires s0.stack[3] == 0xd2b

    requires s0.stack[8] == 0xd57

    requires s0.stack[12] == 0x880

    requires s0.stack[15] == 0x831

    requires s0.stack[21] == 0x799

    requires s0.stack[28] == 0x588

    requires s0.stack[32] == 0x463

    requires s0.stack[36] == 0x193

    requires s0.stack[38] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(8) == 0xd57;
      assert s1.Peek(12) == 0x880;
      assert s1.Peek(15) == 0x831;
      assert s1.Peek(21) == 0x799;
      assert s1.Peek(28) == 0x588;
      assert s1.Peek(32) == 0x463;
      assert s1.Peek(36) == 0x193;
      assert s1.Peek(38) == 0x8c;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s478(s2, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 207
    * Starting at 0xc19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 41

    requires s0.stack[4] == 0xd2b

    requires s0.stack[9] == 0xd57

    requires s0.stack[13] == 0x880

    requires s0.stack[16] == 0x831

    requires s0.stack[22] == 0x799

    requires s0.stack[29] == 0x588

    requires s0.stack[33] == 0x463

    requires s0.stack[37] == 0x193

    requires s0.stack[39] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(9) == 0xd57;
      assert s1.Peek(13) == 0x880;
      assert s1.Peek(16) == 0x831;
      assert s1.Peek(22) == 0x799;
      assert s1.Peek(29) == 0x588;
      assert s1.Peek(33) == 0x463;
      assert s1.Peek(37) == 0x193;
      assert s1.Peek(39) == 0x8c;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c34);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s480(s7, gas - 1)
      else
        ExecuteFromCFGNode_s479(s7, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 208
    * Starting at 0xc22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 41

    requires s0.stack[4] == 0xd2b

    requires s0.stack[9] == 0xd57

    requires s0.stack[13] == 0x880

    requires s0.stack[16] == 0x831

    requires s0.stack[22] == 0x799

    requires s0.stack[29] == 0x588

    requires s0.stack[33] == 0x463

    requires s0.stack[37] == 0x193

    requires s0.stack[39] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xd2b;
      assert s1.Peek(10) == 0xd57;
      assert s1.Peek(14) == 0x880;
      assert s1.Peek(17) == 0x831;
      assert s1.Peek(23) == 0x799;
      assert s1.Peek(30) == 0x588;
      assert s1.Peek(34) == 0x463;
      assert s1.Peek(38) == 0x193;
      assert s1.Peek(40) == 0x8c;
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
      assert s11.Peek(5) == 0xd2b;
      assert s11.Peek(10) == 0xd57;
      assert s11.Peek(14) == 0x880;
      assert s11.Peek(17) == 0x831;
      assert s11.Peek(23) == 0x799;
      assert s11.Peek(30) == 0x588;
      assert s11.Peek(34) == 0x463;
      assert s11.Peek(38) == 0x193;
      assert s11.Peek(40) == 0x8c;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0c19);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s478(s15, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 209
    * Starting at 0xc34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 41

    requires s0.stack[4] == 0xd2b

    requires s0.stack[9] == 0xd57

    requires s0.stack[13] == 0x880

    requires s0.stack[16] == 0x831

    requires s0.stack[22] == 0x799

    requires s0.stack[29] == 0x588

    requires s0.stack[33] == 0x463

    requires s0.stack[37] == 0x193

    requires s0.stack[39] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(9) == 0xd57;
      assert s1.Peek(13) == 0x880;
      assert s1.Peek(16) == 0x831;
      assert s1.Peek(22) == 0x799;
      assert s1.Peek(29) == 0x588;
      assert s1.Peek(33) == 0x463;
      assert s1.Peek(37) == 0x193;
      assert s1.Peek(39) == 0x8c;
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
      ExecuteFromCFGNode_s481(s11, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 227
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 36

    requires s0.stack[4] == 0xd57

    requires s0.stack[8] == 0x880

    requires s0.stack[11] == 0x831

    requires s0.stack[17] == 0x799

    requires s0.stack[24] == 0x588

    requires s0.stack[28] == 0x463

    requires s0.stack[32] == 0x193

    requires s0.stack[34] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd57;
      assert s1.Peek(8) == 0x880;
      assert s1.Peek(11) == 0x831;
      assert s1.Peek(17) == 0x799;
      assert s1.Peek(24) == 0x588;
      assert s1.Peek(28) == 0x463;
      assert s1.Peek(32) == 0x193;
      assert s1.Peek(34) == 0x8c;
      var s2 := Push2(s1, 0x0d34);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0cf7);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s5, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 223
    * Starting at 0xcf7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 38

    requires s0.stack[1] == 0xd34

    requires s0.stack[6] == 0xd57

    requires s0.stack[10] == 0x880

    requires s0.stack[13] == 0x831

    requires s0.stack[19] == 0x799

    requires s0.stack[26] == 0x588

    requires s0.stack[30] == 0x463

    requires s0.stack[34] == 0x193

    requires s0.stack[36] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd34;
      assert s1.Peek(6) == 0xd57;
      assert s1.Peek(10) == 0x880;
      assert s1.Peek(13) == 0x831;
      assert s1.Peek(19) == 0x799;
      assert s1.Peek(26) == 0x588;
      assert s1.Peek(30) == 0x463;
      assert s1.Peek(34) == 0x193;
      assert s1.Peek(36) == 0x8c;
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
      assert s11.Peek(0) == 0xd34;
      assert s11.Peek(7) == 0xd57;
      assert s11.Peek(11) == 0x880;
      assert s11.Peek(14) == 0x831;
      assert s11.Peek(20) == 0x799;
      assert s11.Peek(27) == 0x588;
      assert s11.Peek(31) == 0x463;
      assert s11.Peek(35) == 0x193;
      assert s11.Peek(37) == 0x8c;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s14, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 228
    * Starting at 0xd34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[5] == 0xd57

    requires s0.stack[9] == 0x880

    requires s0.stack[12] == 0x831

    requires s0.stack[18] == 0x799

    requires s0.stack[25] == 0x588

    requires s0.stack[29] == 0x463

    requires s0.stack[33] == 0x193

    requires s0.stack[35] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd57;
      assert s1.Peek(9) == 0x880;
      assert s1.Peek(12) == 0x831;
      assert s1.Peek(18) == 0x799;
      assert s1.Peek(25) == 0x588;
      assert s1.Peek(29) == 0x463;
      assert s1.Peek(33) == 0x193;
      assert s1.Peek(35) == 0x8c;
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
      ExecuteFromCFGNode_s484(s11, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 230
    * Starting at 0xd57
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0x880

    requires s0.stack[7] == 0x831

    requires s0.stack[13] == 0x799

    requires s0.stack[20] == 0x588

    requires s0.stack[24] == 0x463

    requires s0.stack[28] == 0x193

    requires s0.stack[30] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x880;
      assert s1.Peek(7) == 0x831;
      assert s1.Peek(13) == 0x799;
      assert s1.Peek(20) == 0x588;
      assert s1.Peek(24) == 0x463;
      assert s1.Peek(28) == 0x193;
      assert s1.Peek(30) == 0x8c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s8, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 139
    * Starting at 0x880
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x880 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x831

    requires s0.stack[9] == 0x799

    requires s0.stack[16] == 0x588

    requires s0.stack[20] == 0x463

    requires s0.stack[24] == 0x193

    requires s0.stack[26] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x831;
      assert s1.Peek(9) == 0x799;
      assert s1.Peek(16) == 0x588;
      assert s1.Peek(20) == 0x463;
      assert s1.Peek(24) == 0x193;
      assert s1.Peek(26) == 0x8c;
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

  /** Node 486
    * Segment Id for this node is: 121
    * Starting at 0x783
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[9] == 0x588

    requires s0.stack[13] == 0x463

    requires s0.stack[17] == 0x193

    requires s0.stack[19] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x588;
      assert s1.Peek(13) == 0x463;
      assert s1.Peek(17) == 0x193;
      assert s1.Peek(19) == 0x8c;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s442(s4, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 43
    * Starting at 0x198
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x198 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8c;
      var s2 := Push2(s1, 0x01a0);
      var s3 := Push2(s2, 0x0126);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s488(s4, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 35
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x1a0

    requires s0.stack[2] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a0;
      assert s1.Peek(2) == 0x8c;
      var s2 := Push2(s1, 0x012e);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s4, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 75
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x1a0

    requires s0.stack[3] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x1a0;
      assert s1.Peek(3) == 0x8c;
      var s2 := Push2(s1, 0x0348);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s4, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x348

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x1a0

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x348;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x1a0;
      assert s1.Peek(4) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s8, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x348

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x1a0

    requires s0.stack[7] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x348;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x1a0;
      assert s1.Peek(7) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s9, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x348

    requires s0.stack[3] == 0x12e

    requires s0.stack[4] == 0x1a0

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(3) == 0x12e;
      assert s1.Peek(4) == 0x1a0;
      assert s1.Peek(6) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x348;
      assert s11.Peek(3) == 0x12e;
      assert s11.Peek(4) == 0x1a0;
      assert s11.Peek(6) == 0x8c;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s493(s17, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 76
    * Starting at 0x348
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x1a0

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x1a0;
      assert s1.Peek(4) == 0x8c;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x03b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s503(s9, gas - 1)
      else
        ExecuteFromCFGNode_s494(s9, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 77
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x1a0

    requires s0.stack[3] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x1a0;
      assert s1.Peek(4) == 0x8c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0aa2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s11, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 187
    * Starting at 0xaa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x3ac

    requires s0.stack[2] == 0x12e

    requires s0.stack[3] == 0x1a0

    requires s0.stack[5] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ac;
      assert s1.Peek(2) == 0x12e;
      assert s1.Peek(3) == 0x1a0;
      assert s1.Peek(5) == 0x8c;
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
      assert s11.Peek(4) == 0x3ac;
      assert s11.Peek(5) == 0x12e;
      assert s11.Peek(6) == 0x1a0;
      assert s11.Peek(8) == 0x8c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ab9);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0a80);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s496(s18, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 184
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xab9

    requires s0.stack[4] == 0x3ac

    requires s0.stack[5] == 0x12e

    requires s0.stack[6] == 0x1a0

    requires s0.stack[8] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab9;
      assert s1.Peek(4) == 0x3ac;
      assert s1.Peek(5) == 0x12e;
      assert s1.Peek(6) == 0x1a0;
      assert s1.Peek(8) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0a8c);
      var s4 := Push1(s3, 0x42);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s497(s7, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xa8c

    requires s0.stack[5] == 0xab9

    requires s0.stack[8] == 0x3ac

    requires s0.stack[9] == 0x12e

    requires s0.stack[10] == 0x1a0

    requires s0.stack[12] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8c;
      assert s1.Peek(5) == 0xab9;
      assert s1.Peek(8) == 0x3ac;
      assert s1.Peek(9) == 0x12e;
      assert s1.Peek(10) == 0x1a0;
      assert s1.Peek(12) == 0x8c;
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
      assert s11.Peek(0) == 0xa8c;
      assert s11.Peek(6) == 0xab9;
      assert s11.Peek(9) == 0x3ac;
      assert s11.Peek(10) == 0x12e;
      assert s11.Peek(11) == 0x1a0;
      assert s11.Peek(13) == 0x8c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s15, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 185
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xab9

    requires s0.stack[6] == 0x3ac

    requires s0.stack[7] == 0x12e

    requires s0.stack[8] == 0x1a0

    requires s0.stack[10] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab9;
      assert s1.Peek(6) == 0x3ac;
      assert s1.Peek(7) == 0x12e;
      assert s1.Peek(8) == 0x1a0;
      assert s1.Peek(10) == 0x8c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a97);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0a0c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s7, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 183
    * Starting at 0xa0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xa97

    requires s0.stack[4] == 0xab9

    requires s0.stack[7] == 0x3ac

    requires s0.stack[8] == 0x12e

    requires s0.stack[9] == 0x1a0

    requires s0.stack[11] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa97;
      assert s1.Peek(4) == 0xab9;
      assert s1.Peek(7) == 0x3ac;
      assert s1.Peek(8) == 0x12e;
      assert s1.Peek(9) == 0x1a0;
      assert s1.Peek(11) == 0x8c;
      var s2 := Push32(s1, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa97;
      assert s11.Peek(4) == 0xab9;
      assert s11.Peek(7) == 0x3ac;
      assert s11.Peek(8) == 0x12e;
      assert s11.Peek(9) == 0x1a0;
      assert s11.Peek(11) == 0x8c;
      var s12 := Push32(s11, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s18, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 186
    * Starting at 0xa97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xab9

    requires s0.stack[5] == 0x3ac

    requires s0.stack[6] == 0x12e

    requires s0.stack[7] == 0x1a0

    requires s0.stack[9] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab9;
      assert s1.Peek(5) == 0x3ac;
      assert s1.Peek(6) == 0x12e;
      assert s1.Peek(7) == 0x1a0;
      assert s1.Peek(9) == 0x8c;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s10, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 188
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x3ac

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x1a0

    requires s0.stack[7] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ac;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x1a0;
      assert s1.Peek(7) == 0x8c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s7, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 78
    * Starting at 0x3ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x1a0

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x1a0;
      assert s1.Peek(4) == 0x8c;
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

  /** Node 503
    * Segment Id for this node is: 79
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x1a0

    requires s0.stack[3] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x1a0;
      assert s1.Peek(3) == 0x8c;
      var s2 := Push2(s1, 0x03bd);
      var s3 := Push2(s2, 0x04b6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s504(s4, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 99
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3bd

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x1a0

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bd;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x1a0;
      assert s1.Peek(4) == 0x8c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s505(s2, gas - 1)
  }

  /** Node 505
    * Segment Id for this node is: 80
    * Starting at 0x3bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x1a0

    requires s0.stack[3] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x1a0;
      assert s1.Peek(3) == 0x8c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s506(s2, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 36
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x1a0

    requires s0.stack[2] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a0;
      assert s1.Peek(2) == 0x8c;
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0139);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s507(s5, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x139

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x1a0

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x1a0;
      assert s1.Peek(4) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s508(s5, gas - 1)
  }

  /** Node 508
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x1a0

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x1a0;
      assert s1.Peek(6) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s509(s8, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x139

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x1a0

    requires s0.stack[9] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x139;
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x1a0;
      assert s1.Peek(9) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s9, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x139

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x1a0

    requires s0.stack[8] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x139;
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x1a0;
      assert s1.Peek(8) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x139;
      assert s11.Peek(5) == 0x13e;
      assert s11.Peek(6) == 0x1a0;
      assert s11.Peek(8) == 0x8c;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s511(s17, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x1a0

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x1a0;
      assert s1.Peek(6) == 0x8c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s5, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 37
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x1a0

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x1a0;
      assert s1.Peek(4) == 0x8c;
      var s2 := Push2(s1, 0x03cd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s3, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 83
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x1a0

    requires s0.stack[4] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x1a0;
      assert s1.Peek(4) == 0x8c;
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
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x1a0;
      assert s11.Peek(10) == 0x8c;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x03e8);
      assert s21.Peek(0) == 0x3e8;
      assert s21.Peek(5) == 0x13e;
      assert s21.Peek(6) == 0x1a0;
      assert s21.Peek(8) == 0x8c;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s515(s22, gas - 1)
      else
        ExecuteFromCFGNode_s514(s22, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 84
    * Starting at 0x3e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x1a0

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x13e;
      assert s1.Peek(5) == 0x1a0;
      assert s1.Peek(7) == 0x8c;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 515
    * Segment Id for this node is: 85
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x1a0

    requires s0.stack[6] == 0x8c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x1a0;
      assert s1.Peek(6) == 0x8c;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 516
    * Segment Id for this node is: 7
    * Starting at 0x4d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x005c);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s546(s4, gas - 1)
      else
        ExecuteFromCFGNode_s517(s4, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 8
    * Starting at 0x53
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x005a);
      assert s1.Peek(0) == 0x5a;
      var s2 := Push2(s1, 0x0126);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s518(s3, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 35
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5a;
      var s2 := Push2(s1, 0x012e);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s519(s4, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 75
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x5a;
      var s2 := Push2(s1, 0x0348);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s4, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x348

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x348;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s521(s8, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x348

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x348;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s522(s9, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x348

    requires s0.stack[3] == 0x12e

    requires s0.stack[4] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(3) == 0x12e;
      assert s1.Peek(4) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x348;
      assert s11.Peek(3) == 0x12e;
      assert s11.Peek(4) == 0x5a;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s523(s17, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 76
    * Starting at 0x348
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x5a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x03b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s533(s9, gas - 1)
      else
        ExecuteFromCFGNode_s524(s9, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 77
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x5a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0aa2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s525(s11, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 187
    * Starting at 0xaa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x3ac

    requires s0.stack[2] == 0x12e

    requires s0.stack[3] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ac;
      assert s1.Peek(2) == 0x12e;
      assert s1.Peek(3) == 0x5a;
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
      assert s11.Peek(4) == 0x3ac;
      assert s11.Peek(5) == 0x12e;
      assert s11.Peek(6) == 0x5a;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ab9);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0a80);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s18, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 184
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0xab9

    requires s0.stack[4] == 0x3ac

    requires s0.stack[5] == 0x12e

    requires s0.stack[6] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab9;
      assert s1.Peek(4) == 0x3ac;
      assert s1.Peek(5) == 0x12e;
      assert s1.Peek(6) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0a8c);
      var s4 := Push1(s3, 0x42);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s7, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xa8c

    requires s0.stack[5] == 0xab9

    requires s0.stack[8] == 0x3ac

    requires s0.stack[9] == 0x12e

    requires s0.stack[10] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8c;
      assert s1.Peek(5) == 0xab9;
      assert s1.Peek(8) == 0x3ac;
      assert s1.Peek(9) == 0x12e;
      assert s1.Peek(10) == 0x5a;
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
      assert s11.Peek(0) == 0xa8c;
      assert s11.Peek(6) == 0xab9;
      assert s11.Peek(9) == 0x3ac;
      assert s11.Peek(10) == 0x12e;
      assert s11.Peek(11) == 0x5a;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s528(s15, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 185
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xab9

    requires s0.stack[6] == 0x3ac

    requires s0.stack[7] == 0x12e

    requires s0.stack[8] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab9;
      assert s1.Peek(6) == 0x3ac;
      assert s1.Peek(7) == 0x12e;
      assert s1.Peek(8) == 0x5a;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a97);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0a0c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s529(s7, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 183
    * Starting at 0xa0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xa97

    requires s0.stack[4] == 0xab9

    requires s0.stack[7] == 0x3ac

    requires s0.stack[8] == 0x12e

    requires s0.stack[9] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa97;
      assert s1.Peek(4) == 0xab9;
      assert s1.Peek(7) == 0x3ac;
      assert s1.Peek(8) == 0x12e;
      assert s1.Peek(9) == 0x5a;
      var s2 := Push32(s1, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa97;
      assert s11.Peek(4) == 0xab9;
      assert s11.Peek(7) == 0x3ac;
      assert s11.Peek(8) == 0x12e;
      assert s11.Peek(9) == 0x5a;
      var s12 := Push32(s11, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s530(s18, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 186
    * Starting at 0xa97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xab9

    requires s0.stack[5] == 0x3ac

    requires s0.stack[6] == 0x12e

    requires s0.stack[7] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab9;
      assert s1.Peek(5) == 0x3ac;
      assert s1.Peek(6) == 0x12e;
      assert s1.Peek(7) == 0x5a;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s531(s10, gas - 1)
  }

  /** Node 531
    * Segment Id for this node is: 188
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x3ac

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ac;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x5a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s532(s7, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 78
    * Starting at 0x3ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x5a;
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

  /** Node 533
    * Segment Id for this node is: 79
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x5a;
      var s2 := Push2(s1, 0x03bd);
      var s3 := Push2(s2, 0x04b6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s534(s4, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 99
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x3bd

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bd;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x5a;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s535(s2, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 80
    * Starting at 0x3bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x5a;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s2, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 36
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5a;
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0139);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s537(s5, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x139

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s538(s5, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s8, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x139

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x139;
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s9, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x139

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x139;
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x139;
      assert s11.Peek(5) == 0x13e;
      assert s11.Peek(6) == 0x5a;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s541(s17, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x5a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s5, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 37
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x5a;
      var s2 := Push2(s1, 0x03cd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s543(s3, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 83
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x5a;
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
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x5a;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x03e8);
      assert s21.Peek(0) == 0x3e8;
      assert s21.Peek(5) == 0x13e;
      assert s21.Peek(6) == 0x5a;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s545(s22, gas - 1)
      else
        ExecuteFromCFGNode_s544(s22, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 84
    * Starting at 0x3e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x13e;
      assert s1.Peek(5) == 0x5a;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 545
    * Segment Id for this node is: 85
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x5a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x5a;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 546
    * Segment Id for this node is: 10
    * Starting at 0x5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0064);
      var s3 := Push2(s2, 0x0126);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s4, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 35
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push2(s1, 0x012e);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s548(s4, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 75
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x64;
      var s2 := Push2(s1, 0x0348);
      var s3 := Push2(s2, 0x03ec);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s549(s4, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 86
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x348

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x348;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0418);
      var s4 := Push32(s3, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s550(s8, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x418

    requires s0.stack[3] == 0x348

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x418;
      assert s1.Peek(3) == 0x348;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x64;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s551(s9, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 87
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x348

    requires s0.stack[3] == 0x12e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(3) == 0x12e;
      assert s1.Peek(4) == 0x64;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x348;
      assert s11.Peek(3) == 0x12e;
      assert s11.Peek(4) == 0x64;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s552(s17, gas - 1)
  }

  /** Node 552
    * Segment Id for this node is: 76
    * Starting at 0x348
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x03b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s562(s9, gas - 1)
      else
        ExecuteFromCFGNode_s553(s9, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 77
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0aa2);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s11, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 187
    * Starting at 0xaa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x3ac

    requires s0.stack[2] == 0x12e

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ac;
      assert s1.Peek(2) == 0x12e;
      assert s1.Peek(3) == 0x64;
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
      assert s11.Peek(4) == 0x3ac;
      assert s11.Peek(5) == 0x12e;
      assert s11.Peek(6) == 0x64;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ab9);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0a80);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s555(s18, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 184
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0xab9

    requires s0.stack[4] == 0x3ac

    requires s0.stack[5] == 0x12e

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab9;
      assert s1.Peek(4) == 0x3ac;
      assert s1.Peek(5) == 0x12e;
      assert s1.Peek(6) == 0x64;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0a8c);
      var s4 := Push1(s3, 0x42);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x09fc);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s556(s7, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 182
    * Starting at 0x9fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xa8c

    requires s0.stack[5] == 0xab9

    requires s0.stack[8] == 0x3ac

    requires s0.stack[9] == 0x12e

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8c;
      assert s1.Peek(5) == 0xab9;
      assert s1.Peek(8) == 0x3ac;
      assert s1.Peek(9) == 0x12e;
      assert s1.Peek(10) == 0x64;
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
      assert s11.Peek(0) == 0xa8c;
      assert s11.Peek(6) == 0xab9;
      assert s11.Peek(9) == 0x3ac;
      assert s11.Peek(10) == 0x12e;
      assert s11.Peek(11) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s557(s15, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 185
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xab9

    requires s0.stack[6] == 0x3ac

    requires s0.stack[7] == 0x12e

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab9;
      assert s1.Peek(6) == 0x3ac;
      assert s1.Peek(7) == 0x12e;
      assert s1.Peek(8) == 0x64;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a97);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0a0c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s558(s7, gas - 1)
  }

  /** Node 558
    * Segment Id for this node is: 183
    * Starting at 0xa0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xa97

    requires s0.stack[4] == 0xab9

    requires s0.stack[7] == 0x3ac

    requires s0.stack[8] == 0x12e

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa97;
      assert s1.Peek(4) == 0xab9;
      assert s1.Peek(7) == 0x3ac;
      assert s1.Peek(8) == 0x12e;
      assert s1.Peek(9) == 0x64;
      var s2 := Push32(s1, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa97;
      assert s11.Peek(4) == 0xab9;
      assert s11.Peek(7) == 0x3ac;
      assert s11.Peek(8) == 0x12e;
      assert s11.Peek(9) == 0x64;
      var s12 := Push32(s11, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s559(s18, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 186
    * Starting at 0xa97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xab9

    requires s0.stack[5] == 0x3ac

    requires s0.stack[6] == 0x12e

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab9;
      assert s1.Peek(5) == 0x3ac;
      assert s1.Peek(6) == 0x12e;
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s560(s10, gas - 1)
  }

  /** Node 560
    * Segment Id for this node is: 188
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x3ac

    requires s0.stack[4] == 0x12e

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ac;
      assert s1.Peek(4) == 0x12e;
      assert s1.Peek(5) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s561(s7, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 78
    * Starting at 0x3ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
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

  /** Node 562
    * Segment Id for this node is: 79
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x64;
      var s2 := Push2(s1, 0x03bd);
      var s3 := Push2(s2, 0x04b6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s563(s4, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 99
    * Starting at 0x4b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x3bd

    requires s0.stack[1] == 0x12e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3bd;
      assert s1.Peek(1) == 0x12e;
      assert s1.Peek(2) == 0x64;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s2, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 80
    * Starting at 0x3bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x12e

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12e;
      assert s1.Peek(1) == 0x64;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s565(s2, gas - 1)
  }

  /** Node 565
    * Segment Id for this node is: 36
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0139);
      var s4 := Push2(s3, 0x03bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s566(s5, gas - 1)
  }

  /** Node 566
    * Segment Id for this node is: 81
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x139

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x64;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03c8);
      var s4 := Push2(s3, 0x04b8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s567(s5, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 100
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x3c8

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c8;
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x64;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04e4);
      var s4 := Push32(s3, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s5 := Push0(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x050b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s568(s8, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 102
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x4e4

    requires s0.stack[3] == 0x3c8

    requires s0.stack[5] == 0x139

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e4;
      assert s1.Peek(3) == 0x3c8;
      assert s1.Peek(5) == 0x139;
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x64;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s9, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 101
    * Starting at 0x4e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x3c8

    requires s0.stack[4] == 0x139

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c8;
      assert s1.Peek(4) == 0x139;
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x64;
      var s2 := Push0(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x3c8;
      assert s11.Peek(4) == 0x139;
      assert s11.Peek(5) == 0x13e;
      assert s11.Peek(6) == 0x64;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s570(s17, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 82
    * Starting at 0x3c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x139

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s571(s5, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 37
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x64;
      var s2 := Push2(s1, 0x03cd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s572(s3, gas - 1)
  }

  /** Node 572
    * Segment Id for this node is: 83
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13e

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      assert s1.Peek(2) == 0x64;
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
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x64;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Push0(s17);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x03e8);
      assert s21.Peek(0) == 0x3e8;
      assert s21.Peek(5) == 0x13e;
      assert s21.Peek(6) == 0x64;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s574(s22, gas - 1)
      else
        ExecuteFromCFGNode_s573(s22, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 84
    * Starting at 0x3e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x13e;
      assert s1.Peek(5) == 0x64;
      var s2 := Push0(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 574
    * Segment Id for this node is: 85
    * Starting at 0x3e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x13e

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      assert s1.Peek(4) == 0x64;
      var s2 := ReturnDataSize(s1);
      var s3 := Push0(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
