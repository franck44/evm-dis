include "../../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: STOP Segment
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
      var s1 := Push20(s0, 0xea55728d3d4c8c2677a510a4e9f635ce82c7e2e2);
      var s2 := Address(s1);
      var s3 := Eq(s2);
      var s4 := Push1(s3, 0x80);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x00);
      var s8 := Dup1(s7);
      var s9 := Revert(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }
}
