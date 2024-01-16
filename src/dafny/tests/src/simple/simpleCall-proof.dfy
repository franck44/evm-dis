
include "/Users/franck/development/evm-dis/src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
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
      var s1 := PushN(s0, 1, 0x07);
      assert s1.stack[0] == 0x7;
      var s2 := PushN(s1, 1, 0x08);
      assert s2.stack[1] == 0x7;
      var s3 := PushN(s2, 1, 0x10);
      assert s3.stack[0] == 0x10;
      assert s3.stack[2] == 0x7;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s1(s4, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 2
    * Starting at 0x10
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 2

    requires s0.stack[1] == 0x7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x7;
      var s2 := Swap(s1, 1);
      assert s2.stack[0] == 0x7;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s3, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 1
    * Starting at 0x7
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7 as nat
    // Stack requirements for this node.
    requires s0.IsValid()
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x20);
      var s5 := PushN(s4, 1, 0x40);
      var s6 := Return(s5);
      // Segment is terminal (Revert, Stop or Return)
      s6
  }
}
