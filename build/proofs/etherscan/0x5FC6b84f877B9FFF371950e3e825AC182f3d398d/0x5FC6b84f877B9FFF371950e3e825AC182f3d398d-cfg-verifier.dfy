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
      var s6 := Push2(s5, 0x004c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s321(s7, gas - 1)
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
      var s6 := Push4(s5, 0x56df5f43);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0051);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s9, gas - 1)
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
      var s2 := Push4(s1, 0x63ed7ea1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0066);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s181(s5, gas - 1)
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
      var s2 := Push4(s1, 0x8fa2a9f0);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0079);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s5, gas - 1)
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
      var s2 := Push4(s1, 0xc4b07d85);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x008c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x4c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 8
    * Segment Id for this node is: 15
    * Starting at 0x8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0064);
      var s3 := Push2(s2, 0x009a);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0d7c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s7, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 188
    * Starting at 0xd7c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x9a

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9a;
      assert s1.Peek(3) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d8e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s10, gas - 1)
      else
        ExecuteFromCFGNode_s10(s10, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 189
    * Starting at 0xd8a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x9a

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x9a;
      assert s1.Peek(5) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 11
    * Segment Id for this node is: 190
    * Starting at 0xd8e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x9a

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9a;
      assert s1.Peek(4) == 0x64;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0d99);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0a59);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s7, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 123
    * Starting at 0xa59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd99

    requires s0.stack[6] == 0x9a

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd99;
      assert s1.Peek(6) == 0x9a;
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0a6e);
      assert s11.Peek(0) == 0xa6e;
      assert s11.Peek(3) == 0xd99;
      assert s11.Peek(8) == 0x9a;
      assert s11.Peek(9) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s12, gas - 1)
      else
        ExecuteFromCFGNode_s13(s12, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 124
    * Starting at 0xa6a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd99

    requires s0.stack[6] == 0x9a

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd99;
      assert s1.Peek(7) == 0x9a;
      assert s1.Peek(8) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 14
    * Segment Id for this node is: 125
    * Starting at 0xa6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd99

    requires s0.stack[6] == 0x9a

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd99;
      assert s1.Peek(6) == 0x9a;
      assert s1.Peek(7) == 0x64;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s3, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 191
    * Starting at 0xd99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x9a

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9a;
      assert s1.Peek(5) == 0x64;
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
    * Segment Id for this node is: 16
    * Starting at 0x9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push2(s1, 0x034b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s3, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 47
    * Starting at 0x34b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x24745215);
      var s5 := Push1(s4, 0xe2);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Address(s8);
      var s10 := Swap1(s9);
      var s11 := Push4(s10, 0x91d14854);
      assert s11.Peek(4) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0371);
      var s14 := Swap1(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Swap1(s15);
      var s17 := Caller(s16);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x04);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0da0);
      assert s21.Peek(0) == 0xda0;
      assert s21.Peek(4) == 0x371;
      assert s21.Peek(8) == 0x64;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s22, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 192
    * Starting at 0xda0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x371

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x371;
      assert s1.Peek(7) == 0x64;
      var s2 := Swap2(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x371;
      assert s11.Peek(7) == 0x64;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s18, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 48
    * Starting at 0x371
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x038e);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s16, gas - 1)
      else
        ExecuteFromCFGNode_s20(s16, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 49
    * Starting at 0x385
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 21
    * Segment Id for this node is: 50
    * Starting at 0x38e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
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
      assert s11.Peek(5) == 0x64;
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
      assert s21.Peek(4) == 0x64;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x03b2);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0db7);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s28, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 193
    * Starting at 0xdb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x3b2

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3b2;
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0dc9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s10, gas - 1)
      else
        ExecuteFromCFGNode_s23(s10, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 194
    * Starting at 0xdc5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x3b2

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x3b2;
      assert s1.Peek(6) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 24
    * Segment Id for this node is: 195
    * Starting at 0xdc9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x3b2

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3b2;
      assert s1.Peek(5) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0d99);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s10, gas - 1)
      else
        ExecuteFromCFGNode_s25(s10, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 196
    * Starting at 0xdd5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x3b2

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x3b2;
      assert s1.Peek(7) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 26
    * Segment Id for this node is: 191
    * Starting at 0xd99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x3b2

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3b2;
      assert s1.Peek(6) == 0x64;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s7, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 51
    * Starting at 0x3b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := Push2(s1, 0x03ce);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s3, gas - 1)
      else
        ExecuteFromCFGNode_s28(s3, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 52
    * Starting at 0x3b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0122);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x122;
      assert s11.Peek(3) == 0x64;
      var s12 := Push2(s11, 0x0dd9);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s13, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 197
    * Starting at 0xdd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x122

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x122;
      assert s1.Peek(3) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x33);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x4c61756e6368506164466163746f72793a204f6e6c792061646d696e2063616e);
      assert s11.Peek(2) == 0x122;
      assert s11.Peek(4) == 0x64;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 19, 0x1031b0b636103a3434b990333ab731ba34b7b7);
      var s17 := Push1(s16, 0x69);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x122;
      assert s21.Peek(5) == 0x64;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s26, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 23
    * Starting at 0x122
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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

  /** Node 31
    * Segment Id for this node is: 53
    * Starting at 0x3ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x03d8);
      var s4 := Push2(s3, 0x0a35);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s5, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 122
    * Starting at 0xa35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x3d8

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3d8;
      assert s1.Peek(3) == 0x64;
      var s2 := Push32(s1, 0x5088c009090a98f2d9c2d802238b83071c81c03fc910569960814159bcc93093);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s4, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 54
    * Starting at 0x3d8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x64;
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
      assert s11.Peek(6) == 0x64;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x04);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(4) == 0x64;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := Pop(s23);
      var s25 := Push1(s24, 0xff);
      var s26 := And(s25);
      var s27 := Push2(s26, 0x0458);
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s28, gas - 1)
      else
        ExecuteFromCFGNode_s34(s28, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 55
    * Starting at 0x3fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x64;
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
      assert s11.Peek(5) == 0x64;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x2a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4c61756e6368506164466163746f72793a204c61756e636850616420646f6573);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x64;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 10, 0x081b9bdd08195e1a5cdd);
      var s24 := Push1(s23, 0xb2);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(3) == 0x64;
      var s32 := Push2(s31, 0x0122);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s33, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 23
    * Starting at 0x122
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x64;
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

  /** Node 36
    * Segment Id for this node is: 56
    * Starting at 0x458
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x458 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup4(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x03);
      var s15 := Dup4(s14);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup2(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(5) == 0x64;
      var s22 := SLoad(s21);
      var s23 := Swap1(s22);
      var s24 := Swap2(s23);
      var s25 := And(s24);
      var s26 := Swap1(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s37(s26, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 57
    * Starting at 0x479
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x479 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
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
      assert s11.Peek(7) == 0x64;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Dup5(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x64;
      var s22 := Dup2(s21);
      var s23 := Lt(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x05d4);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s26, gas - 1)
      else
        ExecuteFromCFGNode_s38(s26, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 58
    * Starting at 0x49c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(5) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup3(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x64;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Dup6(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(7) == 0x64;
      var s22 := SLoad(s21);
      var s23 := Swap2(s22);
      var s24 := Dup7(s23);
      var s25 := And(s24);
      var s26 := Swap2(s25);
      var s27 := Dup4(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Lt(s29);
      var s31 := Push2(s30, 0x04cc);
      assert s31.Peek(0) == 0x4cc;
      assert s31.Peek(9) == 0x64;
      var s32 := JumpI(s31);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s31.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s32, gas - 1)
      else
        ExecuteFromCFGNode_s39(s32, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 59
    * Starting at 0x4c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04cc);
      assert s1.Peek(0) == 0x4cc;
      assert s1.Peek(8) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s3, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x4cc

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4cc;
      assert s1.Peek(8) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4cc;
      assert s11.Peek(10) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 41
    * Segment Id for this node is: 60
    * Starting at 0x4cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Keccak256(s8);
      var s10 := Add(s9);
      var s11 := SLoad(s10);
      assert s11.Peek(6) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := And(s16);
      var s18 := Sub(s17);
      var s19 := Push2(s18, 0x05cc);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s20, gas - 1)
      else
        ExecuteFromCFGNode_s42(s20, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 61
    * Starting at 0x4e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(5) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup3(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Dup1(s12);
      var s14 := Dup6(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Swap2(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(6) == 0x64;
      var s22 := Dup1(s21);
      var s23 := SLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Swap2(s24);
      var s26 := Push2(s25, 0x050f);
      var s27 := Swap2(s26);
      var s28 := Push2(s27, 0x0f8b);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s29, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 213
    * Starting at 0xf8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x50f

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x50f;
      assert s1.Peek(8) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0fac);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s10, gas - 1)
      else
        ExecuteFromCFGNode_s44(s10, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 214
    * Starting at 0xf97
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x50f

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x50f;
      assert s1.Peek(10) == 0x64;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 45
    * Segment Id for this node is: 215
    * Starting at 0xfac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x50f

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50f;
      assert s1.Peek(9) == 0x64;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s6, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 62
    * Starting at 0x50f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x051f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s7, gas - 1)
      else
        ExecuteFromCFGNode_s47(s7, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 63
    * Starting at 0x518
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x518 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x051f);
      assert s1.Peek(0) == 0x51f;
      assert s1.Peek(7) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s3, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x51f

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x51f;
      assert s1.Peek(7) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x51f;
      assert s11.Peek(9) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 49
    * Segment Id for this node is: 64
    * Starting at 0x51f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup1(s6);
      var s8 := Dup4(s7);
      var s9 := Keccak256(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(8) == 0x64;
      var s12 := Add(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := Dup6(s18);
      var s20 := Dup2(s19);
      var s21 := And(s20);
      assert s21.Peek(9) == 0x64;
      var s22 := Dup5(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Dup8(s24);
      var s26 := Add(s25);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := Swap1(s30);
      assert s31.Peek(8) == 0x64;
      var s32 := Swap3(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Swap2(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := And(s38);
      var s40 := Swap2(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s41, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 65
    * Starting at 0x54f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x055e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s6, gas - 1)
      else
        ExecuteFromCFGNode_s51(s6, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 66
    * Starting at 0x557
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x557 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x055e);
      assert s1.Peek(0) == 0x55e;
      assert s1.Peek(8) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s3, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x55e

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x55e;
      assert s1.Peek(8) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x55e;
      assert s11.Peek(10) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 53
    * Segment Id for this node is: 67
    * Starting at 0x55e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup1(s6);
      var s8 := Dup4(s7);
      var s9 := Keccak256(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(9) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := SLoad(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Not(s20);
      assert s21.Peek(10) == 0x64;
      var s22 := And(s21);
      var s23 := Push1(s22, 0x01);
      var s24 := Push1(s23, 0x01);
      var s25 := Push1(s24, 0xa0);
      var s26 := Shl(s25);
      var s27 := Sub(s26);
      var s28 := Swap5(s27);
      var s29 := Dup6(s28);
      var s30 := And(s29);
      var s31 := Or(s30);
      assert s31.Peek(9) == 0x64;
      var s32 := Swap1(s31);
      var s33 := SStore(s32);
      var s34 := Swap2(s33);
      var s35 := Dup5(s34);
      var s36 := And(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x01);
      var s40 := Dup6(s39);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s54(s41, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 68
    * Starting at 0x590
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x590 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Swap2(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Swap1(s4);
      var s6 := Keccak256(s5);
      var s7 := Dup1(s6);
      var s8 := SLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x05a5);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s11, gas - 1)
      else
        ExecuteFromCFGNode_s55(s11, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 69
    * Starting at 0x59e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05a5);
      assert s1.Peek(0) == 0x5a5;
      assert s1.Peek(7) == 0x64;
      var s2 := Push2(s1, 0x0fb2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s3, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 216
    * Starting at 0xfb2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x5a5

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5a5;
      assert s1.Peek(7) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x31);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x5a5;
      assert s11.Peek(9) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 57
    * Segment Id for this node is: 70
    * Starting at 0x5a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Keccak256(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(8) == 0x64;
      var s12 := Not(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Dup1(s15);
      var s17 := SLoad(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0xa0);
      var s21 := Shl(s20);
      assert s21.Peek(11) == 0x64;
      var s22 := Sub(s21);
      var s23 := Not(s22);
      var s24 := And(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := SStore(s28);
      var s30 := Push2(s29, 0x05d4);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s31, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 72
    * Starting at 0x5d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Push4(s10, 0xd0a2f2c4);
      assert s11.Peek(6) == 0x64;
      var s12 := Push1(s11, 0x40);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Push4(s14, 0xffffffff);
      var s16 := And(s15);
      var s17 := Push1(s16, 0xe0);
      var s18 := Shl(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x04);
      assert s21.Peek(8) == 0x64;
      var s22 := Add(s21);
      var s23 := Push1(s22, 0x00);
      var s24 := Push1(s23, 0x40);
      var s25 := MLoad(s24);
      var s26 := Dup1(s25);
      var s27 := Dup4(s26);
      var s28 := Sub(s27);
      var s29 := Dup2(s28);
      var s30 := Dup7(s29);
      var s31 := Gas(s30);
      assert s31.Peek(13) == 0x64;
      var s32 := StaticCall(s31);
      var s33 := IsZero(s32);
      var s34 := Dup1(s33);
      var s35 := IsZero(s34);
      var s36 := Push2(s35, 0x0615);
      var s37 := JumpI(s36);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s36.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s37, gas - 1)
      else
        ExecuteFromCFGNode_s59(s37, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 73
    * Starting at 0x60c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 60
    * Segment Id for this node is: 74
    * Starting at 0x615
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x615 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup3(s9);
      var s11 := ReturnDataCopy(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := Push1(s11, 0x1f);
      var s13 := ReturnDataSize(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0x1f);
      var s18 := Not(s17);
      var s19 := And(s18);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x64;
      var s22 := Push1(s21, 0x40);
      var s23 := MStore(s22);
      var s24 := Push2(s23, 0x063d);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Push2(s29, 0x0fc8);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s31, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 217
    * Starting at 0xfc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x63d

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x63d;
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0fdb);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s11, gas - 1)
      else
        ExecuteFromCFGNode_s62(s11, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 218
    * Starting at 0xfd7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x63d

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x63d;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 63
    * Segment Id for this node is: 219
    * Starting at 0xfdb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x63d

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x63d;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup3(s1);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(6) == 0x63d;
      assert s11.Peek(11) == 0x64;
      var s12 := Push2(s11, 0x0ff1);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s13, gas - 1)
      else
        ExecuteFromCFGNode_s64(s13, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 220
    * Starting at 0xfed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x63d

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x63d;
      assert s1.Peek(11) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 65
    * Segment Id for this node is: 221
    * Starting at 0xff1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x63d

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x63d;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup4(s1);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := Dup6(s6);
      var s8 := SGt(s7);
      var s9 := Push2(s8, 0x1002);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s10, gas - 1)
      else
        ExecuteFromCFGNode_s66(s10, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 222
    * Starting at 0xffe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x63d

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x63d;
      assert s1.Peek(11) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 67
    * Segment Id for this node is: 223
    * Starting at 0x1002
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1002 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x63d

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x63d;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x1010);
      var s5 := Push2(s4, 0x0be1);
      var s6 := Dup3(s5);
      var s7 := Push2(s6, 0x0aef);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s8, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 135
    * Starting at 0xaef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xbe1

    requires s0.stack[2] == 0x1010

    requires s0.stack[9] == 0x63d

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbe1;
      assert s1.Peek(2) == 0x1010;
      assert s1.Peek(9) == 0x63d;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x40);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0b08);
      assert s11.Peek(0) == 0xb08;
      assert s11.Peek(4) == 0xbe1;
      assert s11.Peek(5) == 0x1010;
      assert s11.Peek(12) == 0x63d;
      assert s11.Peek(17) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s12, gas - 1)
      else
        ExecuteFromCFGNode_s69(s12, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 136
    * Starting at 0xb01
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xbe1

    requires s0.stack[3] == 0x1010

    requires s0.stack[10] == 0x63d

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b08);
      assert s1.Peek(0) == 0xb08;
      assert s1.Peek(3) == 0xbe1;
      assert s1.Peek(4) == 0x1010;
      assert s1.Peek(11) == 0x63d;
      assert s1.Peek(16) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s3, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xb08

    requires s0.stack[3] == 0xbe1

    requires s0.stack[4] == 0x1010

    requires s0.stack[11] == 0x63d

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb08;
      assert s1.Peek(3) == 0xbe1;
      assert s1.Peek(4) == 0x1010;
      assert s1.Peek(11) == 0x63d;
      assert s1.Peek(16) == 0x64;
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
      assert s11.Peek(2) == 0xb08;
      assert s11.Peek(5) == 0xbe1;
      assert s11.Peek(6) == 0x1010;
      assert s11.Peek(13) == 0x63d;
      assert s11.Peek(18) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 71
    * Segment Id for this node is: 137
    * Starting at 0xb08
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xbe1

    requires s0.stack[3] == 0x1010

    requires s0.stack[10] == 0x63d

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbe1;
      assert s1.Peek(3) == 0x1010;
      assert s1.Peek(10) == 0x63d;
      assert s1.Peek(15) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s8, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 154
    * Starting at 0xbe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1010

    requires s0.stack[8] == 0x63d

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1010;
      assert s1.Peek(8) == 0x63d;
      assert s1.Peek(13) == 0x64;
      var s2 := Push2(s1, 0x0abf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 132
    * Starting at 0xabf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1010

    requires s0.stack[8] == 0x63d

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1010;
      assert s1.Peek(8) == 0x63d;
      assert s1.Peek(13) == 0x64;
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
      assert s11.Peek(3) == 0x1010;
      assert s11.Peek(10) == 0x63d;
      assert s11.Peek(15) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x40);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup2(s16);
      var s18 := Gt(s17);
      var s19 := Dup3(s18);
      var s20 := Dup3(s19);
      var s21 := Lt(s20);
      assert s21.Peek(5) == 0x1010;
      assert s21.Peek(12) == 0x63d;
      assert s21.Peek(17) == 0x64;
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0ae7);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s25, gas - 1)
      else
        ExecuteFromCFGNode_s74(s25, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 133
    * Starting at 0xae0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1010

    requires s0.stack[10] == 0x63d

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ae7);
      assert s1.Peek(0) == 0xae7;
      assert s1.Peek(4) == 0x1010;
      assert s1.Peek(11) == 0x63d;
      assert s1.Peek(16) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s3, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xae7

    requires s0.stack[4] == 0x1010

    requires s0.stack[11] == 0x63d

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xae7;
      assert s1.Peek(4) == 0x1010;
      assert s1.Peek(11) == 0x63d;
      assert s1.Peek(16) == 0x64;
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
      assert s11.Peek(2) == 0xae7;
      assert s11.Peek(6) == 0x1010;
      assert s11.Peek(13) == 0x63d;
      assert s11.Peek(18) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 76
    * Segment Id for this node is: 134
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1010

    requires s0.stack[10] == 0x63d

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1010;
      assert s1.Peek(10) == 0x63d;
      assert s1.Peek(15) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s7, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 224
    * Starting at 0x1010
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1010 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x63d

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x63d;
      assert s1.Peek(12) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x05);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Shl(s8);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x63d;
      assert s11.Peek(12) == 0x64;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup4(s14);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Dup8(s18);
      var s20 := Dup4(s19);
      var s21 := Gt(s20);
      assert s21.Peek(9) == 0x63d;
      assert s21.Peek(14) == 0x64;
      var s22 := IsZero(s21);
      var s23 := Push2(s22, 0x102f);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s24, gas - 1)
      else
        ExecuteFromCFGNode_s78(s24, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 225
    * Starting at 0x102b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x63d

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(9) == 0x63d;
      assert s1.Peek(14) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 79
    * Segment Id for this node is: 226
    * Starting at 0x102f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x63d

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x63d;
      assert s1.Peek(13) == 0x64;
      var s2 := Swap3(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := Swap3(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s5, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 227
    * Starting at 0x1034
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1034 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x63d

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x63d;
      assert s1.Peek(13) == 0x64;
      var s2 := Dup3(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1056);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s7, gas - 1)
      else
        ExecuteFromCFGNode_s81(s7, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 228
    * Starting at 0x103d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x63d

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x63d;
      assert s1.Peek(14) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Push2(s2, 0x1047);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x0a59);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s6, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 123
    * Starting at 0xa59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1047

    requires s0.stack[11] == 0x63d

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1047;
      assert s1.Peek(11) == 0x63d;
      assert s1.Peek(16) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0a6e);
      assert s11.Peek(0) == 0xa6e;
      assert s11.Peek(3) == 0x1047;
      assert s11.Peek(13) == 0x63d;
      assert s11.Peek(18) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s12, gas - 1)
      else
        ExecuteFromCFGNode_s83(s12, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 124
    * Starting at 0xa6a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1047

    requires s0.stack[11] == 0x63d

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1047;
      assert s1.Peek(12) == 0x63d;
      assert s1.Peek(17) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 84
    * Segment Id for this node is: 125
    * Starting at 0xa6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1047

    requires s0.stack[11] == 0x63d

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1047;
      assert s1.Peek(11) == 0x63d;
      assert s1.Peek(16) == 0x64;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s3, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 229
    * Starting at 0x1047
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1047 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x63d

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x63d;
      assert s1.Peek(14) == 0x64;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Swap3(s3);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Dup5(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x63d;
      assert s11.Peek(13) == 0x64;
      var s12 := Push2(s11, 0x1034);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s13, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 230
    * Starting at 0x1056
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1056 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x63d

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x63d;
      assert s1.Peek(13) == 0x64;
      var s2 := Swap(s1, 8);
      var s3 := Swap7(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s11, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 75
    * Starting at 0x63d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s88(s4, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 76
    * Starting at 0x642
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x642 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x08cc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s8, gas - 1)
      else
        ExecuteFromCFGNode_s89(s8, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 77
    * Starting at 0x64c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s90(s1, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 78
    * Starting at 0x64e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Dup5(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup5(s5);
      var s7 := Dup5(s6);
      var s8 := Dup2(s7);
      var s9 := MLoad(s8);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(11) == 0x64;
      var s12 := Push2(s11, 0x0666);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s13, gas - 1)
      else
        ExecuteFromCFGNode_s91(s13, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 79
    * Starting at 0x65f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0666);
      assert s1.Peek(0) == 0x666;
      assert s1.Peek(11) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s3, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x666

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x666;
      assert s1.Peek(11) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x666;
      assert s11.Peek(13) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 93
    * Segment Id for this node is: 80
    * Starting at 0x666
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x666 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(11) == 0x64;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := And(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(8) == 0x64;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Push1(s28, 0x00);
      var s30 := Keccak256(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x64;
      var s32 := SLoad(s31);
      var s33 := Swap1(s32);
      var s34 := Pop(s33);
      var s35 := Dup2(s34);
      var s36 := Lt(s35);
      var s37 := IsZero(s36);
      var s38 := Push2(s37, 0x08c3);
      var s39 := JumpI(s38);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s38.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s39, gas - 1)
      else
        ExecuteFromCFGNode_s94(s39, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 81
    * Starting at 0x69a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup6(s7);
      var s9 := Push1(s8, 0x02);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(9) == 0x64;
      var s12 := Dup6(s11);
      var s13 := Dup6(s12);
      var s14 := Dup2(s13);
      var s15 := MLoad(s14);
      var s16 := Dup2(s15);
      var s17 := Lt(s16);
      var s18 := Push2(s17, 0x06bb);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s19, gas - 1)
      else
        ExecuteFromCFGNode_s95(s19, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 82
    * Starting at 0x6b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06bb);
      assert s1.Peek(0) == 0x6bb;
      assert s1.Peek(12) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s3, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x6bb

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6bb;
      assert s1.Peek(12) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x6bb;
      assert s11.Peek(14) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 97
    * Segment Id for this node is: 83
    * Starting at 0x6bb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(12) == 0x64;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := And(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(9) == 0x64;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Push1(s28, 0x00);
      var s30 := Keccak256(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(9) == 0x64;
      var s32 := Dup2(s31);
      var s33 := SLoad(s32);
      var s34 := Dup2(s33);
      var s35 := Lt(s34);
      var s36 := Push2(s35, 0x06f4);
      var s37 := JumpI(s36);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s36.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s37, gas - 1)
      else
        ExecuteFromCFGNode_s98(s37, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 84
    * Starting at 0x6ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06f4);
      assert s1.Peek(0) == 0x6f4;
      assert s1.Peek(10) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s3, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x6f4

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6f4;
      assert s1.Peek(10) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x6f4;
      assert s11.Peek(12) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 100
    * Segment Id for this node is: 85
    * Starting at 0x6f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Keccak256(s8);
      var s10 := Add(s9);
      var s11 := SLoad(s10);
      assert s11.Peek(8) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := And(s16);
      var s18 := Sub(s17);
      var s19 := Push2(s18, 0x08bb);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s20, gas - 1)
      else
        ExecuteFromCFGNode_s101(s20, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 86
    * Starting at 0x70f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x02);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Dup2(s6);
      var s8 := MLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Lt(s9);
      var s11 := Push2(s10, 0x0726);
      assert s11.Peek(0) == 0x726;
      assert s11.Peek(12) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s12, gas - 1)
      else
        ExecuteFromCFGNode_s102(s12, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 87
    * Starting at 0x71f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0726);
      assert s1.Peek(0) == 0x726;
      assert s1.Peek(11) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s3, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x726

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x726;
      assert s1.Peek(11) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x726;
      assert s11.Peek(13) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 104
    * Segment Id for this node is: 88
    * Starting at 0x726
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x726 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(11) == 0x64;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := And(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(8) == 0x64;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Push1(s28, 0x00);
      var s30 := Keccak256(s29);
      var s31 := Push1(s30, 0x01);
      assert s31.Peek(8) == 0x64;
      var s32 := Dup7(s31);
      var s33 := Push1(s32, 0x02);
      var s34 := Add(s33);
      var s35 := Push1(s34, 0x00);
      var s36 := Dup7(s35);
      var s37 := Dup7(s36);
      var s38 := Dup2(s37);
      var s39 := MLoad(s38);
      var s40 := Dup2(s39);
      var s41 := Lt(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s105(s41, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 89
    * Starting at 0x75d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0768);
      assert s1.Peek(0) == 0x768;
      assert s1.Peek(14) == 0x64;
      var s2 := JumpI(s1);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s1.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s2, gas - 1)
      else
        ExecuteFromCFGNode_s106(s2, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 90
    * Starting at 0x761
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x761 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0768);
      assert s1.Peek(0) == 0x768;
      assert s1.Peek(13) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s3, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x768

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x768;
      assert s1.Peek(13) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x768;
      assert s11.Peek(15) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 108
    * Segment Id for this node is: 91
    * Starting at 0x768
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x768 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(13) == 0x64;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := And(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(10) == 0x64;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Push1(s28, 0x00);
      var s30 := Keccak256(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(10) == 0x64;
      var s32 := SLoad(s31);
      var s33 := Swap1(s32);
      var s34 := Pop(s33);
      var s35 := Push2(s34, 0x079e);
      var s36 := Swap2(s35);
      var s37 := Swap1(s36);
      var s38 := Push2(s37, 0x0f8b);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s39, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 213
    * Starting at 0xf8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x79e

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x79e;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0fac);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s10, gas - 1)
      else
        ExecuteFromCFGNode_s110(s10, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 214
    * Starting at 0xf97
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x79e

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x79e;
      assert s1.Peek(12) == 0x64;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 111
    * Segment Id for this node is: 215
    * Starting at 0xfac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x79e

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x79e;
      assert s1.Peek(11) == 0x64;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s6, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 92
    * Starting at 0x79e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x07ae);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s115(s7, gas - 1)
      else
        ExecuteFromCFGNode_s113(s7, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 93
    * Starting at 0x7a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x07ae);
      assert s1.Peek(0) == 0x7ae;
      assert s1.Peek(9) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s3, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x7ae

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x7ae;
      assert s1.Peek(9) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x7ae;
      assert s11.Peek(11) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 115
    * Segment Id for this node is: 94
    * Starting at 0x7ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Keccak256(s7);
      var s9 := Add(s8);
      var s10 := SLoad(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(9) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Swap1(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(9) == 0x64;
      var s22 := Push1(s21, 0x02);
      var s23 := Dup9(s22);
      var s24 := Add(s23);
      var s25 := Swap2(s24);
      var s26 := Dup7(s25);
      var s27 := Swap1(s26);
      var s28 := Dup7(s27);
      var s29 := Swap1(s28);
      var s30 := Dup2(s29);
      var s31 := Lt(s30);
      assert s31.Peek(12) == 0x64;
      var s32 := Push2(s31, 0x07de);
      var s33 := JumpI(s32);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s32.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s33, gas - 1)
      else
        ExecuteFromCFGNode_s116(s33, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 95
    * Starting at 0x7d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x07de);
      assert s1.Peek(0) == 0x7de;
      assert s1.Peek(12) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s3, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x7de

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x7de;
      assert s1.Peek(12) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x7de;
      assert s11.Peek(14) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 118
    * Segment Id for this node is: 96
    * Starting at 0x7de
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(12) == 0x64;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := And(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(9) == 0x64;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Push1(s28, 0x00);
      var s30 := Keccak256(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(9) == 0x64;
      var s32 := Dup2(s31);
      var s33 := SLoad(s32);
      var s34 := Dup2(s33);
      var s35 := Lt(s34);
      var s36 := Push2(s35, 0x0817);
      var s37 := JumpI(s36);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s36.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s37, gas - 1)
      else
        ExecuteFromCFGNode_s119(s37, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 97
    * Starting at 0x810
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x810 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0817);
      assert s1.Peek(0) == 0x817;
      assert s1.Peek(10) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s3, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x817

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x817;
      assert s1.Peek(10) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x817;
      assert s11.Peek(12) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 121
    * Segment Id for this node is: 98
    * Starting at 0x817
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x817 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push1(s5, 0x00);
      var s7 := Keccak256(s6);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Push2(s9, 0x0100);
      var s11 := Exp(s10);
      assert s11.Peek(9) == 0x64;
      var s12 := Dup2(s11);
      var s13 := SLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0xa0);
      var s18 := Shl(s17);
      var s19 := Sub(s18);
      var s20 := Mul(s19);
      var s21 := Not(s20);
      assert s21.Peek(11) == 0x64;
      var s22 := And(s21);
      var s23 := Swap1(s22);
      var s24 := Dup4(s23);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0xa0);
      var s28 := Shl(s27);
      var s29 := Sub(s28);
      var s30 := And(s29);
      var s31 := Mul(s30);
      assert s31.Peek(10) == 0x64;
      var s32 := Or(s31);
      var s33 := Swap1(s32);
      var s34 := SStore(s33);
      var s35 := Pop(s34);
      var s36 := Dup5(s35);
      var s37 := Push1(s36, 0x02);
      var s38 := Add(s37);
      var s39 := Push1(s38, 0x00);
      var s40 := Dup5(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s122(s41, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 99
    * Starting at 0x84e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(11) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x085d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s6, gas - 1)
      else
        ExecuteFromCFGNode_s123(s6, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 100
    * Starting at 0x856
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x856 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x085d);
      assert s1.Peek(0) == 0x85d;
      assert s1.Peek(11) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s3, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x85d

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x85d;
      assert s1.Peek(11) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x85d;
      assert s11.Peek(13) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 125
    * Segment Id for this node is: 101
    * Starting at 0x85d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(11) == 0x64;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := And(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(8) == 0x64;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Push1(s28, 0x00);
      var s30 := Keccak256(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x64;
      var s32 := SLoad(s31);
      var s33 := Dup1(s32);
      var s34 := Push2(s33, 0x0894);
      var s35 := JumpI(s34);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s34.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s35, gas - 1)
      else
        ExecuteFromCFGNode_s126(s35, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 102
    * Starting at 0x88d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0894);
      assert s1.Peek(0) == 0x894;
      assert s1.Peek(9) == 0x64;
      var s2 := Push2(s1, 0x0fb2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s3, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 216
    * Starting at 0xfb2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x894

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x894;
      assert s1.Peek(9) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x31);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x894;
      assert s11.Peek(11) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 128
    * Segment Id for this node is: 103
    * Starting at 0x894
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x894 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Keccak256(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(10) == 0x64;
      var s12 := Not(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Dup1(s15);
      var s17 := SLoad(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0xa0);
      var s21 := Shl(s20);
      assert s21.Peek(13) == 0x64;
      var s22 := Sub(s21);
      var s23 := Not(s22);
      var s24 := And(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := SStore(s28);
      var s30 := Push2(s29, 0x08c3);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s31, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 105
    * Starting at 0x8c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Push2(s4, 0x0642);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s6, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 104
    * Starting at 0x8bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Add(s2);
      var s4 := Push2(s3, 0x064e);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s5, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 106
    * Starting at 0x8cc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s132(s3, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 107
    * Starting at 0x8d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
      var s2 := Dup4(s1);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x09c7);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s8, gas - 1)
      else
        ExecuteFromCFGNode_s133(s8, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 108
    * Starting at 0x8da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(8) == 0x64;
      var s12 := Dup2(s11);
      var s13 := SLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x08f8);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s17, gas - 1)
      else
        ExecuteFromCFGNode_s134(s17, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 109
    * Starting at 0x8f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x08f8);
      assert s1.Peek(0) == 0x8f8;
      assert s1.Peek(9) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s3, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x8f8

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8f8;
      assert s1.Peek(9) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x8f8;
      assert s11.Peek(11) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 136
    * Segment Id for this node is: 110
    * Starting at 0x8f8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Keccak256(s8);
      var s10 := Add(s9);
      var s11 := SLoad(s10);
      assert s11.Peek(7) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := And(s16);
      var s18 := Sub(s17);
      var s19 := Push2(s18, 0x09bf);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s20, gas - 1)
      else
        ExecuteFromCFGNode_s137(s20, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 111
    * Starting at 0x913
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x913 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := SLoad(s1);
      var s3 := Dup5(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0922);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x0f8b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s10, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 213
    * Starting at 0xf8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x922

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x922;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0fac);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s10, gas - 1)
      else
        ExecuteFromCFGNode_s139(s10, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 214
    * Starting at 0xf97
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x922

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x922;
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 140
    * Segment Id for this node is: 215
    * Starting at 0xfac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x922

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x922;
      assert s1.Peek(10) == 0x64;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s6, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 112
    * Starting at 0x922
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x922 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0932);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s7, gas - 1)
      else
        ExecuteFromCFGNode_s142(s7, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 113
    * Starting at 0x92b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0932);
      assert s1.Peek(0) == 0x932;
      assert s1.Peek(8) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s3, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x932

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x932;
      assert s1.Peek(8) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x932;
      assert s11.Peek(10) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 144
    * Segment Id for this node is: 114
    * Starting at 0x932
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x932 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Keccak256(s8);
      var s10 := Add(s9);
      var s11 := SLoad(s10);
      assert s11.Peek(6) == 0x64;
      var s12 := Dup5(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := Swap1(s18);
      var s20 := Swap2(s19);
      var s21 := And(s20);
      assert s21.Peek(7) == 0x64;
      var s22 := Swap1(s21);
      var s23 := Dup6(s22);
      var s24 := Swap1(s23);
      var s25 := Dup4(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Lt(s27);
      var s29 := Push2(s28, 0x095e);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s30, gas - 1)
      else
        ExecuteFromCFGNode_s145(s30, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 115
    * Starting at 0x957
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x957 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x095e);
      assert s1.Peek(0) == 0x95e;
      assert s1.Peek(9) == 0x64;
      var s2 := Push2(s1, 0x0f75);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s3, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 212
    * Starting at 0xf75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x95e

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x95e;
      assert s1.Peek(9) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x95e;
      assert s11.Peek(11) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 147
    * Segment Id for this node is: 116
    * Starting at 0x95e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Keccak256(s8);
      var s10 := Add(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(8) == 0x64;
      var s12 := SLoad(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := And(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0x01);
      assert s21.Peek(10) == 0x64;
      var s22 := Push1(s21, 0xa0);
      var s23 := Shl(s22);
      var s24 := Sub(s23);
      var s25 := Swap3(s24);
      var s26 := Swap1(s25);
      var s27 := Swap3(s26);
      var s28 := And(s27);
      var s29 := Swap2(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(8) == 0x64;
      var s32 := Or(s31);
      var s33 := Swap1(s32);
      var s34 := SStore(s33);
      var s35 := Dup4(s34);
      var s36 := SLoad(s35);
      var s37 := Dup5(s36);
      var s38 := Swap1(s37);
      var s39 := Dup1(s38);
      var s40 := Push2(s39, 0x0998);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s41, gas - 1)
      else
        ExecuteFromCFGNode_s148(s41, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 117
    * Starting at 0x991
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x991 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0998);
      assert s1.Peek(0) == 0x998;
      assert s1.Peek(8) == 0x64;
      var s2 := Push2(s1, 0x0fb2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s3, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 216
    * Starting at 0xfb2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x998

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x998;
      assert s1.Peek(8) == 0x64;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x31);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x998;
      assert s11.Peek(10) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 150
    * Segment Id for this node is: 118
    * Starting at 0x998
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x998 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Keccak256(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(9) == 0x64;
      var s12 := Not(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Dup1(s15);
      var s17 := SLoad(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0xa0);
      var s21 := Shl(s20);
      assert s21.Peek(12) == 0x64;
      var s22 := Sub(s21);
      var s23 := Not(s22);
      var s24 := And(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := SStore(s28);
      var s30 := Push2(s29, 0x09c7);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s31, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 120
    * Starting at 0x9c7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup1(s7);
      var s9 := Dup6(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(7) == 0x64;
      var s12 := Dup2(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x03);
      var s16 := Dup7(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(8) == 0x64;
      var s22 := Push1(s21, 0x40);
      var s23 := Dup1(s22);
      var s24 := Dup4(s23);
      var s25 := Keccak256(s24);
      var s26 := Dup1(s25);
      var s27 := SLoad(s26);
      var s28 := Push1(s27, 0x01);
      var s29 := Push1(s28, 0x01);
      var s30 := Push1(s29, 0xa0);
      var s31 := Shl(s30);
      assert s31.Peek(13) == 0x64;
      var s32 := Sub(s31);
      var s33 := Not(s32);
      var s34 := And(s33);
      var s35 := Swap1(s34);
      var s36 := SStore(s35);
      var s37 := Push1(s36, 0x04);
      var s38 := Dup9(s37);
      var s39 := Add(s38);
      var s40 := Swap1(s39);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s152(s41, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 121
    * Starting at 0x9fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Keccak256(s3);
      var s5 := Dup1(s4);
      var s6 := SLoad(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := SStore(s10);
      assert s11.Peek(8) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Swap3(s12);
      var s14 := Dup6(s13);
      var s15 := And(s14);
      var s16 := Swap3(s15);
      var s17 := Push32(s16, 0x6d60b2ca94430fa886f56a3735557fd6bcbaaad6cfaf8cd2793ea06a31e1fdf0);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Log3(s19);
      var s21 := Pop(s20);
      assert s21.Peek(3) == 0x64;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s25, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 10
    * Starting at 0x64
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64 as nat
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

  /** Node 154
    * Segment Id for this node is: 119
    * Starting at 0x9bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Add(s2);
      var s4 := Push2(s3, 0x08d0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s5, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 71
    * Starting at 0x5cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Add(s2);
      var s4 := Push2(s3, 0x0479);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s5, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 13
    * Starting at 0x79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0064);
      var s3 := Push2(s2, 0x0087);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0d7c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s7, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 188
    * Starting at 0xd7c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x87

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x87;
      assert s1.Peek(3) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d8e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s10, gas - 1)
      else
        ExecuteFromCFGNode_s158(s10, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 189
    * Starting at 0xd8a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x87

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x87;
      assert s1.Peek(5) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 159
    * Segment Id for this node is: 190
    * Starting at 0xd8e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x87

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x87;
      assert s1.Peek(4) == 0x64;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0d99);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0a59);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s7, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 123
    * Starting at 0xa59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd99

    requires s0.stack[6] == 0x87

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd99;
      assert s1.Peek(6) == 0x87;
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0a6e);
      assert s11.Peek(0) == 0xa6e;
      assert s11.Peek(3) == 0xd99;
      assert s11.Peek(8) == 0x87;
      assert s11.Peek(9) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s12, gas - 1)
      else
        ExecuteFromCFGNode_s161(s12, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 124
    * Starting at 0xa6a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd99

    requires s0.stack[6] == 0x87

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd99;
      assert s1.Peek(7) == 0x87;
      assert s1.Peek(8) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 162
    * Segment Id for this node is: 125
    * Starting at 0xa6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd99

    requires s0.stack[6] == 0x87

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd99;
      assert s1.Peek(6) == 0x87;
      assert s1.Peek(7) == 0x64;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s3, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 191
    * Starting at 0xd99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x87

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x87;
      assert s1.Peek(5) == 0x64;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s7, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 14
    * Starting at 0x87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push2(s1, 0x0268);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s3, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 38
    * Starting at 0x268
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x268 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x24745215);
      var s5 := Push1(s4, 0xe2);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Address(s8);
      var s10 := Swap1(s9);
      var s11 := Push4(s10, 0x91d14854);
      assert s11.Peek(4) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x028e);
      var s14 := Swap1(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Swap1(s15);
      var s17 := Caller(s16);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x04);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0da0);
      assert s21.Peek(0) == 0xda0;
      assert s21.Peek(4) == 0x28e;
      assert s21.Peek(8) == 0x64;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s22, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 192
    * Starting at 0xda0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28e

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x28e;
      assert s1.Peek(7) == 0x64;
      var s2 := Swap2(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x28e;
      assert s11.Peek(7) == 0x64;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s18, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 39
    * Starting at 0x28e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x02ab);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s16, gas - 1)
      else
        ExecuteFromCFGNode_s168(s16, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 40
    * Starting at 0x2a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 169
    * Segment Id for this node is: 41
    * Starting at 0x2ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
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
      assert s11.Peek(5) == 0x64;
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
      assert s21.Peek(4) == 0x64;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02cf);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0db7);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s28, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 193
    * Starting at 0xdb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x2cf

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2cf;
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0dc9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s10, gas - 1)
      else
        ExecuteFromCFGNode_s171(s10, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 194
    * Starting at 0xdc5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x2cf

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2cf;
      assert s1.Peek(6) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 172
    * Segment Id for this node is: 195
    * Starting at 0xdc9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x2cf

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2cf;
      assert s1.Peek(5) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0d99);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s10, gas - 1)
      else
        ExecuteFromCFGNode_s173(s10, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 196
    * Starting at 0xdd5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x2cf

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x2cf;
      assert s1.Peek(7) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 174
    * Segment Id for this node is: 191
    * Starting at 0xd99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x2cf

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2cf;
      assert s1.Peek(6) == 0x64;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s7, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 42
    * Starting at 0x2cf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := Push2(s1, 0x02eb);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s3, gas - 1)
      else
        ExecuteFromCFGNode_s176(s3, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 43
    * Starting at 0x2d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0122);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x122;
      assert s11.Peek(3) == 0x64;
      var s12 := Push2(s11, 0x0dd9);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s13, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 44
    * Starting at 0x2eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f5);
      var s4 := Push2(s3, 0x0a35);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s5, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 122
    * Starting at 0xa35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x2f5

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f5;
      assert s1.Peek(3) == 0x64;
      var s2 := Push32(s1, 0x5088c009090a98f2d9c2d802238b83071c81c03fc910569960814159bcc93093);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s4, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 45
    * Starting at 0x2f5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x64;
      var s2 := Push1(s1, 0x15);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := SLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(6) == 0x64;
      var s12 := Dup6(s11);
      var s13 := Dup2(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0xa0);
      var s18 := Shl(s17);
      var s19 := Sub(s18);
      var s20 := Not(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(9) == 0x64;
      var s22 := And(s21);
      var s23 := Dup2(s22);
      var s24 := Or(s23);
      var s25 := Swap1(s24);
      var s26 := Swap4(s25);
      var s27 := SStore(s26);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Swap4(s29);
      var s31 := Swap5(s30);
      assert s31.Peek(7) == 0x64;
      var s32 := Pop(s31);
      var s33 := And(s32);
      var s34 := Swap2(s33);
      var s35 := Dup3(s34);
      var s36 := Swap1(s35);
      var s37 := Push32(s36, 0x161a11d78e4c8a98c15b73ea9fd62ecc47a26992a28ca57d3307f1568dd637de);
      var s38 := Swap1(s37);
      var s39 := Push1(s38, 0x00);
      var s40 := Swap1(s39);
      var s41 := Log3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s180(s41, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 46
    * Starting at 0x347
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x347 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s4, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 11
    * Starting at 0x66
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0064);
      var s3 := Push2(s2, 0x0074);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0d63);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 185
    * Starting at 0xd63
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x74

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x74;
      assert s1.Peek(3) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d75);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s10, gas - 1)
      else
        ExecuteFromCFGNode_s183(s10, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 186
    * Starting at 0xd71
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x74

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x74;
      assert s1.Peek(5) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 184
    * Segment Id for this node is: 187
    * Starting at 0xd75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x74

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x74;
      assert s1.Peek(4) == 0x64;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s7, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 12
    * Starting at 0x74
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push2(s1, 0x0193);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s3, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 30
    * Starting at 0x193
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x24745215);
      var s5 := Push1(s4, 0xe2);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Address(s8);
      var s10 := Swap1(s9);
      var s11 := Push4(s10, 0x91d14854);
      assert s11.Peek(4) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x01b9);
      var s14 := Swap1(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Swap1(s15);
      var s17 := Caller(s16);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x04);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0da0);
      assert s21.Peek(0) == 0xda0;
      assert s21.Peek(4) == 0x1b9;
      assert s21.Peek(8) == 0x64;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s22, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 192
    * Starting at 0xda0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1b9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1b9;
      assert s1.Peek(7) == 0x64;
      var s2 := Swap2(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x1b9;
      assert s11.Peek(7) == 0x64;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s18, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 31
    * Starting at 0x1b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x01d6);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s190(s16, gas - 1)
      else
        ExecuteFromCFGNode_s189(s16, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 32
    * Starting at 0x1cd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 190
    * Segment Id for this node is: 33
    * Starting at 0x1d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
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
      assert s11.Peek(5) == 0x64;
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
      assert s21.Peek(4) == 0x64;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x01fa);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0db7);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s28, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 193
    * Starting at 0xdb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x1fa

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fa;
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0dc9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s10, gas - 1)
      else
        ExecuteFromCFGNode_s192(s10, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 194
    * Starting at 0xdc5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x1fa

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1fa;
      assert s1.Peek(6) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 193
    * Segment Id for this node is: 195
    * Starting at 0xdc9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x1fa

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1fa;
      assert s1.Peek(5) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0d99);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s10, gas - 1)
      else
        ExecuteFromCFGNode_s194(s10, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 196
    * Starting at 0xdd5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x1fa

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1fa;
      assert s1.Peek(7) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 195
    * Segment Id for this node is: 191
    * Starting at 0xd99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x1fa

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1fa;
      assert s1.Peek(6) == 0x64;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s7, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 34
    * Starting at 0x1fa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := Push2(s1, 0x0216);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s3, gas - 1)
      else
        ExecuteFromCFGNode_s197(s3, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 35
    * Starting at 0x1ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0122);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x122;
      assert s11.Peek(3) == 0x64;
      var s12 := Push2(s11, 0x0dd9);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s13, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 36
    * Starting at 0x216
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0220);
      var s4 := Push2(s3, 0x0a35);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s5, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 122
    * Starting at 0xa35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x220

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x220;
      assert s1.Peek(3) == 0x64;
      var s2 := Push32(s1, 0x5088c009090a98f2d9c2d802238b83071c81c03fc910569960814159bcc93093);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s4, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 37
    * Starting at 0x220
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x220 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x64;
      var s2 := Push1(s1, 0x16);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Dup5(s7);
      var s9 := Swap1(s8);
      var s10 := SStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Dup5(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Swap2(s15);
      var s17 := Swap3(s16);
      var s18 := Pop(s17);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x64;
      var s22 := Push32(s21, 0x4d420eda3e385a85c138f1832f16132e4712245c18b02ab7a9f3af6a1b13ef38);
      var s23 := Swap1(s22);
      var s24 := Push1(s23, 0x20);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0x40);
      var s27 := MLoad(s26);
      var s28 := Dup1(s27);
      var s29 := Swap2(s28);
      var s30 := Sub(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x64;
      var s32 := Log2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s36, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 8
    * Starting at 0x51
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0064);
      var s3 := Push2(s2, 0x005f);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0b81);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s7, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 146
    * Starting at 0xb81
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x5f

    requires s0.stack[3] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5f;
      assert s1.Peek(3) == 0x64;
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
      assert s11.Peek(7) == 0x5f;
      assert s11.Peek(8) == 0x64;
      var s12 := Push2(s11, 0x0b97);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s13, gas - 1)
      else
        ExecuteFromCFGNode_s203(s13, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 147
    * Starting at 0xb93
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x5f

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x5f;
      assert s1.Peek(8) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 204
    * Segment Id for this node is: 148
    * Starting at 0xb97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x5f

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x5f;
      assert s1.Peek(7) == 0x64;
      var s2 := Push2(s1, 0x0ba1);
      var s3 := Dup6(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push2(s4, 0x0a59);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s6, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 123
    * Starting at 0xa59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xba1

    requires s0.stack[8] == 0x5f

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xba1;
      assert s1.Peek(8) == 0x5f;
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0a6e);
      assert s11.Peek(0) == 0xa6e;
      assert s11.Peek(3) == 0xba1;
      assert s11.Peek(10) == 0x5f;
      assert s11.Peek(11) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s12, gas - 1)
      else
        ExecuteFromCFGNode_s206(s12, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 124
    * Starting at 0xa6a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xba1

    requires s0.stack[8] == 0x5f

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xba1;
      assert s1.Peek(9) == 0x5f;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 207
    * Segment Id for this node is: 125
    * Starting at 0xa6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xba1

    requires s0.stack[8] == 0x5f

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xba1;
      assert s1.Peek(8) == 0x5f;
      assert s1.Peek(9) == 0x64;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s3, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 149
    * Starting at 0xba1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x5f

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x5f;
      assert s1.Peek(7) == 0x64;
      var s2 := Dup5(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap4(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x40);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x5f;
      assert s11.Peek(9) == 0x64;
      var s12 := Dup7(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Dup2(s14);
      var s16 := Lt(s15);
      var s17 := IsZero(s16);
      var s18 := Push2(s17, 0x0bbe);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s210(s19, gas - 1)
      else
        ExecuteFromCFGNode_s209(s19, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 150
    * Starting at 0xbba
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5f

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x5f;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 210
    * Segment Id for this node is: 151
    * Starting at 0xbbe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5f

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5f;
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Dup8(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(10) == 0x5f;
      assert s11.Peek(11) == 0x64;
      var s12 := SLt(s11);
      var s13 := Push2(s12, 0x0bd4);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s14, gas - 1)
      else
        ExecuteFromCFGNode_s211(s14, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 152
    * Starting at 0xbd0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x5f

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(9) == 0x5f;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 212
    * Segment Id for this node is: 153
    * Starting at 0xbd4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x5f

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x5f;
      assert s1.Peek(9) == 0x64;
      var s2 := Push2(s1, 0x0be6);
      var s3 := Push2(s2, 0x0be1);
      var s4 := Dup3(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push2(s5, 0x0aef);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s7, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 135
    * Starting at 0xaef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xbe1

    requires s0.stack[2] == 0xbe6

    requires s0.stack[11] == 0x5f

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbe1;
      assert s1.Peek(2) == 0xbe6;
      assert s1.Peek(11) == 0x5f;
      assert s1.Peek(12) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x40);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0b08);
      assert s11.Peek(0) == 0xb08;
      assert s11.Peek(4) == 0xbe1;
      assert s11.Peek(5) == 0xbe6;
      assert s11.Peek(14) == 0x5f;
      assert s11.Peek(15) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s216(s12, gas - 1)
      else
        ExecuteFromCFGNode_s214(s12, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 136
    * Starting at 0xb01
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xbe1

    requires s0.stack[3] == 0xbe6

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b08);
      assert s1.Peek(0) == 0xb08;
      assert s1.Peek(3) == 0xbe1;
      assert s1.Peek(4) == 0xbe6;
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s3, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xb08

    requires s0.stack[3] == 0xbe1

    requires s0.stack[4] == 0xbe6

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb08;
      assert s1.Peek(3) == 0xbe1;
      assert s1.Peek(4) == 0xbe6;
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
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
      assert s11.Peek(2) == 0xb08;
      assert s11.Peek(5) == 0xbe1;
      assert s11.Peek(6) == 0xbe6;
      assert s11.Peek(15) == 0x5f;
      assert s11.Peek(16) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 216
    * Segment Id for this node is: 137
    * Starting at 0xb08
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xbe1

    requires s0.stack[3] == 0xbe6

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbe1;
      assert s1.Peek(3) == 0xbe6;
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s8, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 154
    * Starting at 0xbe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xbe6

    requires s0.stack[10] == 0x5f

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbe6;
      assert s1.Peek(10) == 0x5f;
      assert s1.Peek(11) == 0x64;
      var s2 := Push2(s1, 0x0abf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s3, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 132
    * Starting at 0xabf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xbe6

    requires s0.stack[10] == 0x5f

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbe6;
      assert s1.Peek(10) == 0x5f;
      assert s1.Peek(11) == 0x64;
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
      assert s11.Peek(3) == 0xbe6;
      assert s11.Peek(12) == 0x5f;
      assert s11.Peek(13) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x40);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup2(s16);
      var s18 := Gt(s17);
      var s19 := Dup3(s18);
      var s20 := Dup3(s19);
      var s21 := Lt(s20);
      assert s21.Peek(5) == 0xbe6;
      assert s21.Peek(14) == 0x5f;
      assert s21.Peek(15) == 0x64;
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0ae7);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s221(s25, gas - 1)
      else
        ExecuteFromCFGNode_s219(s25, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 133
    * Starting at 0xae0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xbe6

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ae7);
      assert s1.Peek(0) == 0xae7;
      assert s1.Peek(4) == 0xbe6;
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s3, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xae7

    requires s0.stack[4] == 0xbe6

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xae7;
      assert s1.Peek(4) == 0xbe6;
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
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
      assert s11.Peek(2) == 0xae7;
      assert s11.Peek(6) == 0xbe6;
      assert s11.Peek(15) == 0x5f;
      assert s11.Peek(16) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 221
    * Segment Id for this node is: 134
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xbe6

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbe6;
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s7, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 155
    * Starting at 0xbe6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x5f

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x5f;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Dup3(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup1(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(12) == 0x5f;
      assert s11.Peek(13) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Push1(s12, 0x05);
      var s14 := Shl(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := Dup11(s17);
      var s19 := Lt(s18);
      var s20 := IsZero(s19);
      var s21 := Push2(s20, 0x0c04);
      assert s21.Peek(0) == 0xc04;
      assert s21.Peek(12) == 0x5f;
      assert s21.Peek(13) == 0x64;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s224(s22, gas - 1)
      else
        ExecuteFromCFGNode_s223(s22, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 156
    * Starting at 0xc00
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x5f

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(11) == 0x5f;
      assert s1.Peek(12) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 224
    * Segment Id for this node is: 157
    * Starting at 0xc04
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x5f

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x5f;
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s225(s4, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 158
    * Starting at 0xc09
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc09 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x5f

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x5f;
      assert s1.Peek(12) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup5(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push1(s4, 0x05);
      var s6 := Shl(s5);
      var s7 := Dup6(s6);
      var s8 := Add(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(12) == 0x5f;
      assert s11.Peek(13) == 0x64;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s14, gas - 1)
      else
        ExecuteFromCFGNode_s226(s14, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 159
    * Starting at 0xc1b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x5f

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c28);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s228(s7, gas - 1)
      else
        ExecuteFromCFGNode_s227(s7, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 160
    * Starting at 0xc24
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x5f

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 228
    * Segment Id for this node is: 161
    * Starting at 0xc28
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x5f

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x5f;
      assert s1.Peek(12) == 0x64;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Dup2(s6);
      var s8 := Dup14(s7);
      var s9 := Sub(s8);
      var s10 := Push1(s9, 0x1f);
      var s11 := Not(s10);
      assert s11.Peek(15) == 0x5f;
      assert s11.Peek(16) == 0x64;
      var s12 := Add(s11);
      var s13 := SLt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0c40);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s16, gas - 1)
      else
        ExecuteFromCFGNode_s229(s16, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 162
    * Starting at 0xc3c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 230
    * Segment Id for this node is: 163
    * Starting at 0xc40
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Push2(s1, 0x0c48);
      var s3 := Push2(s2, 0x0a97);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s4, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 129
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xc48

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc48;
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x40);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(3) == 0xc48;
      assert s11.Peek(16) == 0x5f;
      assert s11.Peek(17) == 0x64;
      var s12 := Dup2(s11);
      var s13 := Gt(s12);
      var s14 := Dup3(s13);
      var s15 := Dup3(s14);
      var s16 := Lt(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0ab9);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s234(s20, gas - 1)
      else
        ExecuteFromCFGNode_s232(s20, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 130
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xc48

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ab9);
      assert s1.Peek(0) == 0xab9;
      assert s1.Peek(3) == 0xc48;
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s3, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xab9

    requires s0.stack[3] == 0xc48

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xab9;
      assert s1.Peek(3) == 0xc48;
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
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
      assert s11.Peek(2) == 0xab9;
      assert s11.Peek(5) == 0xc48;
      assert s11.Peek(18) == 0x5f;
      assert s11.Peek(19) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 234
    * Segment Id for this node is: 131
    * Starting at 0xab9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xc48

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc48;
      assert s1.Peek(15) == 0x5f;
      assert s1.Peek(16) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s5, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 164
    * Starting at 0xc48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Push2(s1, 0x0c55);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Push2(s6, 0x0a59);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s8, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 123
    * Starting at 0xa59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xc55

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc55;
      assert s1.Peek(15) == 0x5f;
      assert s1.Peek(16) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0a6e);
      assert s11.Peek(0) == 0xa6e;
      assert s11.Peek(3) == 0xc55;
      assert s11.Peek(17) == 0x5f;
      assert s11.Peek(18) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s238(s12, gas - 1)
      else
        ExecuteFromCFGNode_s237(s12, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 124
    * Starting at 0xa6a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xc55

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xc55;
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 238
    * Segment Id for this node is: 125
    * Starting at 0xa6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xc55

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc55;
      assert s1.Peek(15) == 0x5f;
      assert s1.Peek(16) == 0x64;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s3, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 165
    * Starting at 0xc55
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x03);
      var s9 := Push1(s8, 0x40);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(15) == 0x5f;
      assert s11.Peek(16) == 0x64;
      var s12 := CallDataLoad(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x0c6d);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s15, gas - 1)
      else
        ExecuteFromCFGNode_s240(s15, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 166
    * Starting at 0xc69
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(14) == 0x5f;
      assert s1.Peek(15) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 241
    * Segment Id for this node is: 167
    * Starting at 0xc6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Dup7(s9);
      var s11 := Push1(s10, 0x60);
      assert s11.Peek(15) == 0x5f;
      assert s11.Peek(16) == 0x64;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0c88);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s243(s18, gas - 1)
      else
        ExecuteFromCFGNode_s242(s18, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 168
    * Starting at 0xc84
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(14) == 0x5f;
      assert s1.Peek(15) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 243
    * Segment Id for this node is: 169
    * Starting at 0xc88
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Dup13(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(15) == 0x5f;
      assert s11.Peek(16) == 0x64;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := SLt(s13);
      var s15 := Push2(s14, 0x0ca0);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s245(s16, gas - 1)
      else
        ExecuteFromCFGNode_s244(s16, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 170
    * Starting at 0xc9c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(14) == 0x5f;
      assert s1.Peek(15) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 245
    * Segment Id for this node is: 171
    * Starting at 0xca0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Push2(s1, 0x0cb0);
      var s3 := Push2(s2, 0x0be1);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0aef);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s9, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 135
    * Starting at 0xaef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xbe1

    requires s0.stack[2] == 0xcb0

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbe1;
      assert s1.Peek(2) == 0xcb0;
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x40);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0b08);
      assert s11.Peek(0) == 0xb08;
      assert s11.Peek(4) == 0xbe1;
      assert s11.Peek(5) == 0xcb0;
      assert s11.Peek(19) == 0x5f;
      assert s11.Peek(20) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s249(s12, gas - 1)
      else
        ExecuteFromCFGNode_s247(s12, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 136
    * Starting at 0xb01
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xbe1

    requires s0.stack[3] == 0xcb0

    requires s0.stack[17] == 0x5f

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b08);
      assert s1.Peek(0) == 0xb08;
      assert s1.Peek(3) == 0xbe1;
      assert s1.Peek(4) == 0xcb0;
      assert s1.Peek(18) == 0x5f;
      assert s1.Peek(19) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s3, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xb08

    requires s0.stack[3] == 0xbe1

    requires s0.stack[4] == 0xcb0

    requires s0.stack[18] == 0x5f

    requires s0.stack[19] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb08;
      assert s1.Peek(3) == 0xbe1;
      assert s1.Peek(4) == 0xcb0;
      assert s1.Peek(18) == 0x5f;
      assert s1.Peek(19) == 0x64;
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
      assert s11.Peek(2) == 0xb08;
      assert s11.Peek(5) == 0xbe1;
      assert s11.Peek(6) == 0xcb0;
      assert s11.Peek(20) == 0x5f;
      assert s11.Peek(21) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 249
    * Segment Id for this node is: 137
    * Starting at 0xb08
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xbe1

    requires s0.stack[3] == 0xcb0

    requires s0.stack[17] == 0x5f

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbe1;
      assert s1.Peek(3) == 0xcb0;
      assert s1.Peek(17) == 0x5f;
      assert s1.Peek(18) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s8, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 154
    * Starting at 0xbe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xcb0

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcb0;
      assert s1.Peek(15) == 0x5f;
      assert s1.Peek(16) == 0x64;
      var s2 := Push2(s1, 0x0abf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s3, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 132
    * Starting at 0xabf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xcb0

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcb0;
      assert s1.Peek(15) == 0x5f;
      assert s1.Peek(16) == 0x64;
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
      assert s11.Peek(3) == 0xcb0;
      assert s11.Peek(17) == 0x5f;
      assert s11.Peek(18) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x40);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup2(s16);
      var s18 := Gt(s17);
      var s19 := Dup3(s18);
      var s20 := Dup3(s19);
      var s21 := Lt(s20);
      assert s21.Peek(5) == 0xcb0;
      assert s21.Peek(19) == 0x5f;
      assert s21.Peek(20) == 0x64;
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0ae7);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s254(s25, gas - 1)
      else
        ExecuteFromCFGNode_s252(s25, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 133
    * Starting at 0xae0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xcb0

    requires s0.stack[17] == 0x5f

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ae7);
      assert s1.Peek(0) == 0xae7;
      assert s1.Peek(4) == 0xcb0;
      assert s1.Peek(18) == 0x5f;
      assert s1.Peek(19) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s3, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xae7

    requires s0.stack[4] == 0xcb0

    requires s0.stack[18] == 0x5f

    requires s0.stack[19] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xae7;
      assert s1.Peek(4) == 0xcb0;
      assert s1.Peek(18) == 0x5f;
      assert s1.Peek(19) == 0x64;
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
      assert s11.Peek(2) == 0xae7;
      assert s11.Peek(6) == 0xcb0;
      assert s11.Peek(20) == 0x5f;
      assert s11.Peek(21) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 254
    * Segment Id for this node is: 134
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xcb0

    requires s0.stack[17] == 0x5f

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcb0;
      assert s1.Peek(17) == 0x5f;
      assert s1.Peek(18) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s7, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 172
    * Starting at 0xcb0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[14] == 0x5f

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x5f;
      assert s1.Peek(15) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Dup2(s3);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Dup4(s7);
      var s9 := MStore(s8);
      var s10 := Swap1(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(17) == 0x5f;
      assert s11.Peek(18) == 0x64;
      var s12 := Add(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push1(s14, 0x05);
      var s16 := Shl(s15);
      var s17 := Dup5(s16);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Add(s19);
      var s21 := Dup16(s20);
      assert s21.Peek(17) == 0x5f;
      assert s21.Peek(18) == 0x64;
      var s22 := Dup2(s21);
      var s23 := Gt(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0cd3);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s257(s26, gas - 1)
      else
        ExecuteFromCFGNode_s256(s26, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 173
    * Starting at 0xccf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(17) == 0x5f;
      assert s1.Peek(18) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 257
    * Segment Id for this node is: 174
    * Starting at 0xcd3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap5(s4);
      var s6 := Pop(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s258(s6, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 175
    * Starting at 0xcda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0d0c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s262(s7, gas - 1)
      else
        ExecuteFromCFGNode_s259(s7, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 176
    * Starting at 0xce3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      assert s1.Peek(17) == 0x5f;
      assert s1.Peek(18) == 0x64;
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Not(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Eq(s10);
      assert s11.Peek(17) == 0x5f;
      assert s11.Peek(18) == 0x64;
      var s12 := Push2(s11, 0x0cf9);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s13, gas - 1)
      else
        ExecuteFromCFGNode_s260(s13, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 177
    * Starting at 0xcf5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(17) == 0x5f;
      assert s1.Peek(18) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 261
    * Segment Id for this node is: 178
    * Starting at 0xcf9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
      var s2 := Dup5(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup4(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap5(s6);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := Swap5(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(17) == 0x5f;
      assert s11.Peek(18) == 0x64;
      var s12 := Swap3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Push2(s14, 0x0cda);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s16, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 179
    * Starting at 0xd0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Dup5(s7);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(12) == 0x5f;
      assert s11.Peek(13) == 0x64;
      var s12 := Swap3(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Swap3(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c09);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s18, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 180
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x5f

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x5f;
      assert s1.Peek(12) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap6(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x0d34);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Dup8(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd34;
      assert s11.Peek(9) == 0x5f;
      assert s11.Peek(10) == 0x64;
      var s12 := Push2(s11, 0x0a71);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s13, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 126
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xd34

    requires s0.stack[9] == 0x5f

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd34;
      assert s1.Peek(9) == 0x5f;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0a7c);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0a59);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s7, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 123
    * Starting at 0xa59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xa7c

    requires s0.stack[4] == 0xd34

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa7c;
      assert s1.Peek(4) == 0xd34;
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0a6e);
      assert s11.Peek(0) == 0xa6e;
      assert s11.Peek(3) == 0xa7c;
      assert s11.Peek(6) == 0xd34;
      assert s11.Peek(14) == 0x5f;
      assert s11.Peek(15) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s12, gas - 1)
      else
        ExecuteFromCFGNode_s266(s12, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 124
    * Starting at 0xa6a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xa7c

    requires s0.stack[4] == 0xd34

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xa7c;
      assert s1.Peek(5) == 0xd34;
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 267
    * Segment Id for this node is: 125
    * Starting at 0xa6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xa7c

    requires s0.stack[4] == 0xd34

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa7c;
      assert s1.Peek(4) == 0xd34;
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s3, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 127
    * Starting at 0xa7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xd34

    requires s0.stack[10] == 0x5f

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd34;
      assert s1.Peek(10) == 0x5f;
      assert s1.Peek(11) == 0x64;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s5, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 181
    * Starting at 0xd34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x5f

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x5f;
      assert s1.Peek(9) == 0x64;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Gt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0d47);
      assert s11.Peek(0) == 0xd47;
      assert s11.Peek(9) == 0x5f;
      assert s11.Peek(10) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s271(s12, gas - 1)
      else
        ExecuteFromCFGNode_s270(s12, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 182
    * Starting at 0xd43
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5f

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x5f;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 271
    * Segment Id for this node is: 183
    * Starting at 0xd47
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd47 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5f

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5f;
      assert s1.Peek(8) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0d58);
      var s4 := Dup7(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0b12);
      assert s11.Peek(0) == 0xb12;
      assert s11.Peek(3) == 0xd58;
      assert s11.Peek(10) == 0x5f;
      assert s11.Peek(11) == 0x64;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s12, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 138
    * Starting at 0xb12
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xd58

    requires s0.stack[9] == 0x5f

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd58;
      assert s1.Peek(9) == 0x5f;
      assert s1.Peek(10) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0b23);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s274(s9, gas - 1)
      else
        ExecuteFromCFGNode_s273(s9, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 139
    * Starting at 0xb1f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xd58

    requires s0.stack[10] == 0x5f

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xd58;
      assert s1.Peek(11) == 0x5f;
      assert s1.Peek(12) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 274
    * Segment Id for this node is: 140
    * Starting at 0xb23
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xd58

    requires s0.stack[10] == 0x5f

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd58;
      assert s1.Peek(10) == 0x5f;
      assert s1.Peek(11) == 0x64;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(5) == 0xd58;
      assert s11.Peek(12) == 0x5f;
      assert s11.Peek(13) == 0x64;
      var s12 := Push2(s11, 0x0b3c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s277(s13, gas - 1)
      else
        ExecuteFromCFGNode_s275(s13, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 141
    * Starting at 0xb35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xd58

    requires s0.stack[11] == 0x5f

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b3c);
      assert s1.Peek(0) == 0xb3c;
      assert s1.Peek(5) == 0xd58;
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s3, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xb3c

    requires s0.stack[5] == 0xd58

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb3c;
      assert s1.Peek(5) == 0xd58;
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
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
      assert s11.Peek(2) == 0xb3c;
      assert s11.Peek(7) == 0xd58;
      assert s11.Peek(14) == 0x5f;
      assert s11.Peek(15) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 277
    * Segment Id for this node is: 142
    * Starting at 0xb3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xd58

    requires s0.stack[11] == 0x5f

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd58;
      assert s1.Peek(11) == 0x5f;
      assert s1.Peek(12) == 0x64;
      var s2 := Push2(s1, 0x0b4f);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Not(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0abf);
      assert s11.Peek(0) == 0xabf;
      assert s11.Peek(2) == 0xb4f;
      assert s11.Peek(7) == 0xd58;
      assert s11.Peek(14) == 0x5f;
      assert s11.Peek(15) == 0x64;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s12, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 132
    * Starting at 0xabf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xb4f

    requires s0.stack[6] == 0xd58

    requires s0.stack[13] == 0x5f

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb4f;
      assert s1.Peek(6) == 0xd58;
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
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
      assert s11.Peek(3) == 0xb4f;
      assert s11.Peek(8) == 0xd58;
      assert s11.Peek(15) == 0x5f;
      assert s11.Peek(16) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x40);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup2(s16);
      var s18 := Gt(s17);
      var s19 := Dup3(s18);
      var s20 := Dup3(s19);
      var s21 := Lt(s20);
      assert s21.Peek(5) == 0xb4f;
      assert s21.Peek(10) == 0xd58;
      assert s21.Peek(17) == 0x5f;
      assert s21.Peek(18) == 0x64;
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0ae7);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s281(s25, gas - 1)
      else
        ExecuteFromCFGNode_s279(s25, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 133
    * Starting at 0xae0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xb4f

    requires s0.stack[8] == 0xd58

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ae7);
      assert s1.Peek(0) == 0xae7;
      assert s1.Peek(4) == 0xb4f;
      assert s1.Peek(9) == 0xd58;
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
      var s2 := Push2(s1, 0x0a81);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s3, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 128
    * Starting at 0xa81
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xae7

    requires s0.stack[4] == 0xb4f

    requires s0.stack[9] == 0xd58

    requires s0.stack[16] == 0x5f

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xae7;
      assert s1.Peek(4) == 0xb4f;
      assert s1.Peek(9) == 0xd58;
      assert s1.Peek(16) == 0x5f;
      assert s1.Peek(17) == 0x64;
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
      assert s11.Peek(2) == 0xae7;
      assert s11.Peek(6) == 0xb4f;
      assert s11.Peek(11) == 0xd58;
      assert s11.Peek(18) == 0x5f;
      assert s11.Peek(19) == 0x64;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 281
    * Segment Id for this node is: 134
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xb4f

    requires s0.stack[8] == 0xd58

    requires s0.stack[15] == 0x5f

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb4f;
      assert s1.Peek(8) == 0xd58;
      assert s1.Peek(15) == 0x5f;
      assert s1.Peek(16) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s7, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 143
    * Starting at 0xb4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xd58

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd58;
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := Gt(s10);
      assert s11.Peek(6) == 0xd58;
      assert s11.Peek(13) == 0x5f;
      assert s11.Peek(14) == 0x64;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0b64);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s284(s14, gas - 1)
      else
        ExecuteFromCFGNode_s283(s14, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 144
    * Starting at 0xb60
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xd58

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0xd58;
      assert s1.Peek(13) == 0x5f;
      assert s1.Peek(14) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 284
    * Segment Id for this node is: 145
    * Starting at 0xb64
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xd58

    requires s0.stack[12] == 0x5f

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd58;
      assert s1.Peek(12) == 0x5f;
      assert s1.Peek(13) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup6(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0xd58;
      assert s11.Peek(13) == 0x5f;
      assert s11.Peek(14) == 0x64;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Swap3(s20);
      assert s21.Peek(3) == 0xd58;
      assert s21.Peek(11) == 0x5f;
      assert s21.Peek(12) == 0x64;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s25, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 184
    * Starting at 0xd58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5f

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5f;
      assert s1.Peek(8) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap6(s4);
      var s6 := Swap2(s5);
      var s7 := Swap5(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s11, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 9
    * Starting at 0x5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
      var s2 := Push2(s1, 0x009f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s3, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 17
    * Starting at 0x9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x24745215);
      var s5 := Push1(s4, 0xe2);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Address(s8);
      var s10 := Swap1(s9);
      var s11 := Push4(s10, 0x91d14854);
      assert s11.Peek(7) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x00c5);
      var s14 := Swap1(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Swap1(s15);
      var s17 := Caller(s16);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x04);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0da0);
      assert s21.Peek(0) == 0xda0;
      assert s21.Peek(4) == 0xc5;
      assert s21.Peek(11) == 0x64;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s22, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 192
    * Starting at 0xda0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xc5

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc5;
      assert s1.Peek(10) == 0x64;
      var s2 := Swap2(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0xc5;
      assert s11.Peek(10) == 0x64;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s18, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 18
    * Starting at 0xc5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(8) == 0x64;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x00e2);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s291(s16, gas - 1)
      else
        ExecuteFromCFGNode_s290(s16, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 19
    * Starting at 0xd9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 291
    * Segment Id for this node is: 20
    * Starting at 0xe2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x64;
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
      assert s11.Peek(8) == 0x64;
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
      assert s21.Peek(7) == 0x64;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0106);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0db7);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s28, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 193
    * Starting at 0xdb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x106

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x106;
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0dc9);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s294(s10, gas - 1)
      else
        ExecuteFromCFGNode_s293(s10, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 194
    * Starting at 0xdc5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x106

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x106;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 294
    * Segment Id for this node is: 195
    * Starting at 0xdc9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x106

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x106;
      assert s1.Peek(8) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0d99);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s296(s10, gas - 1)
      else
        ExecuteFromCFGNode_s295(s10, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 196
    * Starting at 0xdd5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x106

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x106;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 296
    * Segment Id for this node is: 191
    * Starting at 0xd99
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x106

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x106;
      assert s1.Peek(9) == 0x64;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s7, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 21
    * Starting at 0x106
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
      var s2 := Push2(s1, 0x012b);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s301(s3, gas - 1)
      else
        ExecuteFromCFGNode_s298(s3, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 22
    * Starting at 0x10b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0122);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x122;
      assert s11.Peek(6) == 0x64;
      var s12 := Push2(s11, 0x0dd9);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s13, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 197
    * Starting at 0xdd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x122

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x122;
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x33);
      var s7 := Swap1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push32(s10, 0x4c61756e6368506164466163746f72793a204f6e6c792061646d696e2063616e);
      assert s11.Peek(2) == 0x122;
      assert s11.Peek(7) == 0x64;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 19, 0x1031b0b636103a3434b990333ab731ba34b7b7);
      var s17 := Push1(s16, 0x69);
      var s18 := Shl(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x122;
      assert s21.Peek(8) == 0x64;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x80);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s26, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 23
    * Starting at 0x122
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x64;
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

  /** Node 301
    * Segment Id for this node is: 24
    * Starting at 0x12b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x07e4c707);
      var s5 := Push1(s4, 0xe2);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(8) == 0x64;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := Dup6(s13);
      var s15 := And(s14);
      var s16 := Swap1(s15);
      var s17 := Push4(s16, 0x1f931c1c);
      var s18 := Swap1(s17);
      var s19 := Push2(s18, 0x015b);
      var s20 := Swap1(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(2) == 0x15b;
      assert s21.Peek(9) == 0x64;
      var s22 := Swap1(s21);
      var s23 := Dup7(s22);
      var s24 := Swap1(s23);
      var s25 := Dup7(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Push2(s28, 0x0e72);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s30, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 202
    * Starting at 0xe72
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x15b

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x15b;
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup5(s7);
      var s9 := MStore(s8);
      var s10 := Dup1(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(9) == 0x15b;
      assert s11.Peek(16) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Dup1(s12);
      var s14 := Dup4(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x80);
      var s17 := Swap3(s16);
      var s18 := Pop(s17);
      var s19 := Push1(s18, 0x80);
      var s20 := Dup7(s19);
      var s21 := Add(s20);
      assert s21.Peek(10) == 0x15b;
      assert s21.Peek(17) == 0x64;
      var s22 := Swap2(s21);
      var s23 := Pop(s22);
      var s24 := Push1(s23, 0x80);
      var s25 := Dup2(s24);
      var s26 := Push1(s25, 0x05);
      var s27 := Shl(s26);
      var s28 := Dup8(s27);
      var s29 := Add(s28);
      var s30 := Add(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(11) == 0x15b;
      assert s31.Peek(18) == 0x64;
      var s32 := Dup1(s31);
      var s33 := Dup12(s32);
      var s34 := Add(s33);
      var s35 := Push1(s34, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s303(s35, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 203
    * Starting at 0xe9e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[13] == 0x15b

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x15b;
      assert s1.Peek(20) == 0x64;
      var s2 := Dup5(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0f45);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s310(s7, gas - 1)
      else
        ExecuteFromCFGNode_s304(s7, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 204
    * Starting at 0xea7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[13] == 0x15b

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup10(s0);
      assert s1.Peek(14) == 0x15b;
      assert s1.Peek(21) == 0x64;
      var s2 := Dup5(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x7f);
      var s5 := Not(s4);
      var s6 := Add(s5);
      var s7 := Dup7(s6);
      var s8 := MStore(s7);
      var s9 := Dup2(s8);
      var s10 := MLoad(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(15) == 0x15b;
      assert s11.Peek(22) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := And(s17);
      var s19 := Dup6(s18);
      var s20 := MStore(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(15) == 0x15b;
      assert s21.Peek(22) == 0x64;
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := MLoad(s23);
      var s25 := Dup10(s24);
      var s26 := Dup7(s25);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := Push1(s28, 0x03);
      var s30 := Dup2(s29);
      var s31 := Lt(s30);
      assert s31.Peek(17) == 0x15b;
      assert s31.Peek(24) == 0x64;
      var s32 := Push2(s31, 0x0ee4);
      var s33 := JumpI(s32);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s32.stack[1] > 0 then
        ExecuteFromCFGNode_s306(s33, gas - 1)
      else
        ExecuteFromCFGNode_s305(s33, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 205
    * Starting at 0xecf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[16] == 0x15b

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(17) == 0x15b;
      assert s1.Peek(24) == 0x64;
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

  /** Node 306
    * Segment Id for this node is: 206
    * Starting at 0xee4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[16] == 0x15b

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(16) == 0x15b;
      assert s1.Peek(23) == 0x64;
      var s2 := Dup7(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := Swap2(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(16) == 0x15b;
      assert s11.Peek(23) == 0x64;
      var s12 := Dup7(s11);
      var s13 := Add(s12);
      var s14 := Dup11(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Dup2(s16);
      var s18 := MLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(17) == 0x15b;
      assert s21.Peek(24) == 0x64;
      var s22 := MStore(s21);
      var s23 := Swap1(s22);
      var s24 := Dup5(s23);
      var s25 := Add(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x00);
      var s28 := Swap1(s27);
      var s29 := Dup10(s28);
      var s30 := Dup8(s29);
      var s31 := Add(s30);
      assert s31.Peek(17) == 0x15b;
      assert s31.Peek(24) == 0x64;
      var s32 := Swap1(s31);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s307(s32, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 207
    * Starting at 0xf06
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[17] == 0x15b

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(17) == 0x15b;
      assert s1.Peek(24) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0f30);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s309(s7, gas - 1)
      else
        ExecuteFromCFGNode_s308(s7, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 208
    * Starting at 0xf0f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[17] == 0x15b

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(18) == 0x15b;
      assert s1.Peek(25) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup3(s9);
      var s11 := MStore(s10);
      assert s11.Peek(17) == 0x15b;
      assert s11.Peek(24) == 0x64;
      var s12 := Swap3(s11);
      var s13 := Dup7(s12);
      var s14 := Add(s13);
      var s15 := Swap3(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Swap3(s16);
      var s18 := Swap1(s17);
      var s19 := Swap3(s18);
      var s20 := Add(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(17) == 0x15b;
      assert s21.Peek(24) == 0x64;
      var s22 := Swap1(s21);
      var s23 := Dup7(s22);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Push2(s25, 0x0f06);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s27, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 209
    * Starting at 0xf30
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[17] == 0x15b

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(17) == 0x15b;
      assert s1.Peek(24) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap(s2, 8);
      var s4 := Dup6(s3);
      var s5 := Add(s4);
      var s6 := Swap(s5, 8);
      var s7 := Swap6(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(13) == 0x15b;
      assert s11.Peek(20) == 0x64;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0e9e);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s303(s18, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 210
    * Starting at 0xf45
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[13] == 0x15b

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x15b;
      assert s1.Peek(20) == 0x64;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup11(s8);
      var s10 := And(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(12) == 0x15b;
      assert s11.Peek(19) == 0x64;
      var s12 := Dup9(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup7(s14);
      var s16 := Dup2(s15);
      var s17 := Sub(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup9(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(10) == 0x15b;
      assert s21.Peek(17) == 0x64;
      var s22 := Push2(s21, 0x0f67);
      var s23 := Dup2(s22);
      var s24 := Dup10(s23);
      var s25 := Push2(s24, 0x0e2c);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s26, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 198
    * Starting at 0xe2c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xf67

    requires s0.stack[13] == 0x15b

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf67;
      assert s1.Peek(13) == 0x15b;
      assert s1.Peek(20) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s312(s8, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 199
    * Starting at 0xe36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xf67

    requires s0.stack[16] == 0x15b

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf67;
      assert s1.Peek(16) == 0x15b;
      assert s1.Peek(23) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e52);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s314(s7, gas - 1)
      else
        ExecuteFromCFGNode_s313(s7, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 200
    * Starting at 0xe3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xf67

    requires s0.stack[16] == 0x15b

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0xf67;
      assert s1.Peek(17) == 0x15b;
      assert s1.Peek(24) == 0x64;
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
      assert s11.Peek(9) == 0xf67;
      assert s11.Peek(20) == 0x15b;
      assert s11.Peek(27) == 0x64;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0e36);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s16, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 201
    * Starting at 0xe52
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xf67

    requires s0.stack[16] == 0x15b

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf67;
      assert s1.Peek(16) == 0x15b;
      assert s1.Peek(23) == 0x64;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xf67;
      assert s11.Peek(17) == 0x15b;
      assert s11.Peek(24) == 0x64;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xf67;
      assert s21.Peek(15) == 0x15b;
      assert s21.Peek(22) == 0x64;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s27, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 211
    * Starting at 0xf67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[11] == 0x15b

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x15b;
      assert s1.Peek(18) == 0x64;
      var s2 := Swap(s1, 11);
      var s3 := Swap(s2, 10);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x15b;
      assert s11.Peek(10) == 0x64;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s14, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 25
    * Starting at 0x15b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x64;
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
      assert s11.Peek(14) == 0x64;
      var s12 := ExtCodeSize(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0175);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s318(s17, gas - 1)
      else
        ExecuteFromCFGNode_s317(s17, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 26
    * Starting at 0x171
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(15) == 0x64;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 318
    * Segment Id for this node is: 27
    * Starting at 0x175
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x175 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x64;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0189);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s320(s9, gas - 1)
      else
        ExecuteFromCFGNode_s319(s9, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 28
    * Starting at 0x180
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x180 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 320
    * Segment Id for this node is: 29
    * Starting at 0x189
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x189 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x64;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s10, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 7
    * Starting at 0x4c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c as nat
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
