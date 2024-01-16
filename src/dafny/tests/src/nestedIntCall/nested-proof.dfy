
include "/Users/franck/development/evm-dis/src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module EVMProofObject {

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
    requires s0.IsValid()
    requires s0.Operands() == 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x80);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MStore(s2);
      var s4 := CallValue(s3);
      var s5 := Dup(s4, 1);
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 1, 0x0f);
      assert s7.stack[0] == 0xf;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then

        ExecuteFromCFGNode_s2(s8, gas - 1)
      else
        ExecuteFromCFGNode_s1(s8, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0xb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Dup(s1, 1);
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
    requires s0.IsValid()
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := CallDataSize(s3);
      var s5 := Lt(s4);
      var s6 := PushN(s5, 1, 0x28);
      assert s6.stack[0] == 0x28;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then

        ExecuteFromCFGNode_s15(s7, gas - 1)
      else
        ExecuteFromCFGNode_s3(s7, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup(s4, 1);
      var s6 := PushN(s5, 4, 0xf0fdf834);
      var s7 := Eq(s6);
      var s8 := PushN(s7, 1, 0x2d);
      assert s8.stack[0] == 0x2d;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then

        ExecuteFromCFGNode_s5(s9, gas - 1)
      else
        ExecuteFromCFGNode_s4(s9, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x28
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x3c);
      assert s2.stack[0] == 0x3c;
      var s3 := PushN(s2, 1, 0x38);
      assert s3.stack[0] == 0x38;
      assert s3.stack[1] == 0x3c;
      var s4 := CallDataSize(s3);
      assert s4.stack[1] == 0x38;
      assert s4.stack[2] == 0x3c;
      var s5 := PushN(s4, 1, 0x04);
      assert s5.stack[2] == 0x38;
      assert s5.stack[3] == 0x3c;
      var s6 := PushN(s5, 1, 0x6e);
      assert s6.stack[0] == 0x6e;
      assert s6.stack[3] == 0x38;
      assert s6.stack[4] == 0x3c;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s6(s7, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 12
    * Starting at 0x6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x38

    requires s0.stack[3] == 0x3c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x38;
      assert s1.stack[3] == 0x3c;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[3] == 0x38;
      assert s2.stack[4] == 0x3c;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[4] == 0x38;
      assert s3.stack[5] == 0x3c;
      var s4 := Dup(s3, 3);
      assert s4.stack[5] == 0x38;
      assert s4.stack[6] == 0x3c;
      var s5 := Dup(s4, 5);
      assert s5.stack[6] == 0x38;
      assert s5.stack[7] == 0x3c;
      var s6 := Sub(s5);
      assert s6.stack[5] == 0x38;
      assert s6.stack[6] == 0x3c;
      var s7 := Slt(s6);
      assert s7.stack[4] == 0x38;
      assert s7.stack[5] == 0x3c;
      var s8 := IsZero(s7);
      assert s8.stack[4] == 0x38;
      assert s8.stack[5] == 0x3c;
      var s9 := PushN(s8, 1, 0x7f);
      assert s9.stack[0] == 0x7f;
      assert s9.stack[5] == 0x38;
      assert s9.stack[6] == 0x3c;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then

        ExecuteFromCFGNode_s8(s10, gas - 1)
      else
        ExecuteFromCFGNode_s7(s10, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 13
    * Starting at 0x7b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x38

    requires s0.stack[4] == 0x3c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[4] == 0x38;
      assert s1.stack[5] == 0x3c;
      var s2 := Dup(s1, 1);
      assert s2.stack[5] == 0x38;
      assert s2.stack[6] == 0x3c;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 8
    * Segment Id for this node is: 14
    * Starting at 0x7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x38

    requires s0.stack[4] == 0x3c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x38;
      assert s1.stack[4] == 0x3c;
      var s2 := Pop(s1);
      assert s2.stack[2] == 0x38;
      assert s2.stack[3] == 0x3c;
      var s3 := CallDataLoad(s2);
      assert s3.stack[2] == 0x38;
      assert s3.stack[3] == 0x3c;
      var s4 := Swap(s3, 2);
      assert s4.stack[0] == 0x38;
      assert s4.stack[3] == 0x3c;
      var s5 := Swap(s4, 1);
      assert s5.stack[1] == 0x38;
      assert s5.stack[3] == 0x3c;
      var s6 := Pop(s5);
      assert s6.stack[0] == 0x38;
      assert s6.stack[2] == 0x3c;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s7, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 6
    * Starting at 0x38
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x3c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x3c;
      var s2 := PushN(s1, 1, 0x4e);
      assert s2.stack[0] == 0x4e;
      assert s2.stack[2] == 0x3c;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s3, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 8
    * Starting at 0x4e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x3c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x3c;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[2] == 0x3c;
      var s3 := Dup(s2, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s11(s3, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 9
    * Starting at 0x52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x3c;
      var s2 := Dup(s1, 3);
      assert s2.stack[4] == 0x3c;
      var s3 := Dup(s2, 2);
      assert s3.stack[5] == 0x3c;
      var s4 := Lt(s3);
      assert s4.stack[4] == 0x3c;
      var s5 := IsZero(s4);
      assert s5.stack[4] == 0x3c;
      var s6 := PushN(s5, 1, 0x68);
      assert s6.stack[0] == 0x68;
      assert s6.stack[5] == 0x3c;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then

        ExecuteFromCFGNode_s13(s7, gas - 1)
      else
        ExecuteFromCFGNode_s12(s7, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 10
    * Starting at 0x5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      assert s1.stack[4] == 0x3c;
      var s2 := Dup(s1, 2);
      assert s2.stack[5] == 0x3c;
      var s3 := Add(s2);
      assert s3.stack[4] == 0x3c;
      var s4 := Swap(s3, 1);
      assert s4.stack[4] == 0x3c;
      var s5 := Swap(s4, 2);
      assert s5.stack[4] == 0x3c;
      var s6 := Add(s5);
      assert s6.stack[3] == 0x3c;
      var s7 := Swap(s6, 1);
      assert s7.stack[3] == 0x3c;
      var s8 := PushN(s7, 1, 0x01);
      assert s8.stack[4] == 0x3c;
      var s9 := Add(s8);
      assert s9.stack[3] == 0x3c;
      var s10 := PushN(s9, 1, 0x52);
      assert s10.stack[0] == 0x52;
      assert s10.stack[4] == 0x3c;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s11, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 11
    * Starting at 0x68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x3c;
      var s2 := Pop(s1);
      assert s2.stack[2] == 0x3c;
      var s3 := Swap(s2, 2);
      assert s3.stack[0] == 0x3c;
      var s4 := Swap(s3, 1);
      assert s4.stack[1] == 0x3c;
      var s5 := Pop(s4);
      assert s5.stack[0] == 0x3c;
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s6, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 7
    * Starting at 0x3c
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap(s3, 1);
      var s5 := Dup(s4, 2);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Add(s7);
      var s9 := PushN(s8, 1, 0x40);
      var s10 := MLoad(s9);
      var s11 := Dup(s10, 1);
      var s12 := Swap(s11, 2);
      var s13 := Sub(s12);
      var s14 := Swap(s13, 1);
      var s15 := Return(s14);
      // Segment is terminal (Revert, Stop or Return)
      s15
  }

  /** Node 15
    * Segment Id for this node is: 4
    * Starting at 0x28
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
