
include "../../../AbstractSemantics/AbstractSemantics.dfy"

module EVMProofObject {

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
  function {:opaque} {:verify false} ExecuteFromCFGNode_s0(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x0 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() == 0
    requires s0.Capacity() >= 4

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := PushN(s0, 1, 0x0a);
      assert s1.stack[0] == 0xa;
      var s2 := PushN(s1, 1, 0x08);
      var s3 := PushN(s2, 1, 0x03);
      var s4 := Swap(s3, 1);
      assert s4.stack[2] == 0xa;
      var s5 := PushN(s4, 1, 0x13);
      var s6 := Jump(s5);
      // jump to the successor Next() or Tgt of JUMP;
      ExecuteFromCFGNode_s1(s6, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 2
    * Starting at 0x13
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify false} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() == 3
    requires s0.Capacity() >= 2

    requires s0.stack[2] == 0xa

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0xa;
      var s2 := Swap(s1, 2);
      var s3 := Swap(s2, 1);
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0xa;
      var s5 := Dup(s4, 4);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 1, 0x1f);
      assert s7.stack[0] == 0x1f;
      assert s7.stack[3] == 0xa;
      var s8 := JumpI(s7);
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s4(s8, gas - 1)
      else
        ExecuteFromCFGNode_s2(s8, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 3
    * Starting at 0x1c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: --2
    * Net Capacity Effect: +-2
    */
  function {:opaque} {:verify false} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() == 3
    requires s0.Capacity() >= 0

    requires s0.stack[1] == 0xa

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0xa;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      // jump to the successor Next() or Tgt of JUMP;
      ExecuteFromCFGNode_s3(s3, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 1
    * Starting at 0xa
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: --1
    * Net Capacity Effect: +-1
    */
  function {:opaque} {:verify false} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() == 1
    requires s0.Capacity() >= 1

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x20);
      var s5 := PushN(s4, 1, 0x40);
      var s6 := Return(s5);
      s6
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x1f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify false} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() == 3
    requires s0.Capacity() >= 1

    requires s0.stack[1] == 0xa

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0xa;
      var s2 := Swap(s1, 1);
      var s3 := Swap(s2, 2);
      var s4 := Pop(s3);
      assert s4.stack[1] == 0xa;
      var s5 := Swap(s4, 1);
      var s6 := Push0(s5);
      var s7 := PushN(s6, 1, 0x1c);
      assert s7.stack[0] == 0x1c;
      assert s7.stack[2] == 0xa;
      var s8 := Jump(s7);
      // jump to the successor Next() or Tgt of JUMP;
      ExecuteFromCFGNode_s2(s8, gas - 1)
  }
}
