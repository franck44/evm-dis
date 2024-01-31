include "/Users/franck/development/evm-dis/src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module EVMProofObject {

import opened AbstractSemantics
import opened AbstractState

/** Node 0
* Segment Id for this node is: 0
* Starting at 0x0
* Segment type is: CONT Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +2
* Net Capacity Effect: -2
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
  var s1 := Push0(s0);
  var s2 := Dup(s1, 1);
  //  Go to the next instruction at pc + 1
  ExecuteFromCFGNode_s1(s2, gas - 1)
}

/** Node 1
* Segment Id for this node is: 1
* Starting at 0x2
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x2 as nat
  // Stack requirements for this node.
  requires s0.Operands() >= 2

  decreases gas
{
if gas == 0 then s0
else
  var s1 := JumpDest(s0);
  var s2 := PushN(s1, 1, 0x0a);
  var s3 := Dup(s2, 2);
  var s4 := Lt(s3);
  var s5 := PushN(s4, 1, 0x13);
  assert s5.stack[0] == 0x13;
  var s6 := JumpI(s5);
  // This is a JUMPI segment, determine next pc using second top-most element of stack
  if s5.stack[1] > 0 then
   ExecuteFromCFGNode_s3(s6, gas - 1)
  else
    ExecuteFromCFGNode_s2(s6, gas - 1)
}

/** Node 2
* Segment Id for this node is: 2
* Starting at 0xa
* Segment type is: RETURN Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 0
* Net Stack Effect: -2
* Net Capacity Effect: +2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xa as nat
  // Stack requirements for this node.
  requires s0.Operands() >= 2

  decreases gas
{
if gas == 0 then s0
else
  var s1 := Pop(s0);
  var s2 := PushN(s1, 1, 0x40);
  var s3 := MStore(s2);
  var s4 := PushN(s3, 1, 0x20);
  var s5 := PushN(s4, 1, 0x40);
  var s6 := Return(s5);
  // Segment is terminal (Revert, Stop or Return)
  s6
}

/** Node 3
* Segment Id for this node is: 3
* Starting at 0x13
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x13 as nat
  // Stack requirements for this node.
  requires s0.Operands() >= 2

  decreases gas
{
if gas == 0 then s0
else
  var s1 := JumpDest(s0);
  var s2 := Swap(s1, 1);
  var s3 := PushN(s2, 1, 0x01);
  var s4 := PushN(s3, 1, 0x0a);
  var s5 := Swap(s4, 2);
  var s6 := Add(s5);
  var s7 := Swap(s6, 2);
  var s8 := Swap(s7, 1);
  var s9 := Pop(s8);
  var s10 := PushN(s9, 1, 0x02);
  var s11 := Jump(s10);
  //  JUMP to the target at Peek(0)
  ExecuteFromCFGNode_s1(s11, gas - 1)
}
}
