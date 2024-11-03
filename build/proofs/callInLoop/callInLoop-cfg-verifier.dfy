include "../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
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
      var s1 := Push1(s0, 0x0a);
      assert s1.Peek(0) == 0xa;
      var s2 := Push1(s1, 0x08);
      var s3 := Push1(s2, 0x03);
      assert s3.Peek(2) == 0xa;
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x2f);
      assert s5.Peek(0) == 0x2f;
      assert s5.Peek(3) == 0xa;
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s1(s6, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 6
    * Starting at 0x2f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      assert s3.Peek(1) == 0xa;
      var s4 := Dup1(s3);
      var s5 := Dup(s4, 4);
      assert s5.Peek(3) == 0xa;
      var s6 := Lt(s5);
      var s7 := Push1(s6, 0x3b);
      assert s7.Peek(0) == 0x3b;
      assert s7.Peek(3) == 0xa;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s8, gas - 1)
      else
        ExecuteFromCFGNode_s2(s8, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 7
    * Starting at 0x38
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s3(s3, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 1
    * Starting at 0xa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s4(s2, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 2
    * Starting at 0xc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x0a);
      var s3 := Dup2(s2);
      assert s3.Peek(1) == 0xa;
      var s4 := Lt(s3);
      var s5 := Push1(s4, 0x1d);
      assert s5.Peek(0) == 0x1d;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s6(s6, gas - 1)
      else
        ExecuteFromCFGNode_s5(s6, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 3
    * Starting at 0x14
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push1(s4, 0x40);
      var s6 := Return(s5);
      // Segment is terminal (Revert, Stop or Return)
      s6
  }

  /** Node 6
    * Segment Id for this node is: 4
    * Starting at 0x1d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x2a);
      assert s3.Peek(0) == 0x2a;
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x02);
      assert s5.Peek(2) == 0x2a;
      var s6 := Dup(s5, 4);
      var s7 := Mul(s6);
      assert s7.Peek(2) == 0x2a;
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0x2f);
      assert s9.Peek(0) == 0x2f;
      assert s9.Peek(3) == 0x2a;
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s7(s10, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 6
    * Starting at 0x2f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2a;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      assert s3.Peek(1) == 0x2a;
      var s4 := Dup1(s3);
      var s5 := Dup(s4, 4);
      assert s5.Peek(3) == 0x2a;
      var s6 := Lt(s5);
      var s7 := Push1(s6, 0x3b);
      assert s7.Peek(0) == 0x3b;
      assert s7.Peek(3) == 0x2a;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s8, gas - 1)
      else
        ExecuteFromCFGNode_s8(s8, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 7
    * Starting at 0x38
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x2a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s3, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 5
    * Starting at 0x2a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x0c);
      assert s3.Peek(0) == 0xc;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s4(s4, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 8
    * Starting at 0x3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x2a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2a;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      assert s3.Peek(2) == 0x2a;
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      assert s5.Peek(0) == 0x2a;
      var s6 := Push0(s5);
      var s7 := Push1(s6, 0x38);
      assert s7.Peek(0) == 0x38;
      assert s7.Peek(2) == 0x2a;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s8(s8, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 8
    * Starting at 0x3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      assert s3.Peek(2) == 0xa;
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      assert s5.Peek(0) == 0xa;
      var s6 := Push0(s5);
      var s7 := Push1(s6, 0x38);
      assert s7.Peek(0) == 0x38;
      assert s7.Peek(2) == 0xa;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s8, gas - 1)
  }
}
