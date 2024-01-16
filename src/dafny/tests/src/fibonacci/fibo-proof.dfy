
include "../../../AbstractSemantics/AbstractSemantics.dfy"

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
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s0(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x0 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() == 0

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x80);
  var s2 := PushN(s1, 1, 0x40);
  var s3 := MStore(s2);
  var s4 := CallValue(s3);
  var s5 := Dup(s4, 1);
  var s6 := IsZero(s5);
  var s7 := PushN(s6, 2, 0x0010);
  assert s7.stack[0] == 0x10;
   var s8 := JumpI(s7);
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
  requires s0.IsValid() 
  requires s0.Operands() >= 1

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x00);
  var s2 := Dup(s1, 1);
   var s3 := Revert(s2);
  s3
}

/** Node 2
* Segment Id for this node is: 2
* Starting at 0x10
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 1
* Net Stack Effect: -1
* Net Capacity Effect: +-1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x10 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 1

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  var s2 := Pop(s1);
  var s3 := PushN(s2, 1, 0x04);
  var s4 := CallDataSize(s3);
  var s5 := Lt(s4);
  var s6 := PushN(s5, 2, 0x0036);
  assert s6.stack[0] == 0x36;
   var s7 := JumpI(s6);
  if s6.stack[1] > 0 then 
   ExecuteFromCFGNode_s53(s7, gas - 1)
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
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x1a as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 0

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x00);
  var s2 := CallDataLoad(s1);
  var s3 := PushN(s2, 1, 0xe0);
  var s4 := Shr(s3);
  var s5 := Dup(s4, 1);
  var s6 := PushN(s5, 4, 0x139c7ad4);
  var s7 := Eq(s6);
  var s8 := PushN(s7, 2, 0x003b);
  assert s8.stack[0] == 0x3b;
   var s9 := JumpI(s8);
  if s8.stack[1] > 0 then 
   ExecuteFromCFGNode_s16(s9, gas - 1)
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
  requires s0.IsValid() 
  requires s0.Operands() >= 1

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := Dup(s0, 1);
  var s2 := PushN(s1, 4, 0xc6c2ea17);
  var s3 := Eq(s2);
  var s4 := PushN(s3, 2, 0x0064);
  assert s4.stack[0] == 0x64;
   var s5 := JumpI(s4);
  if s4.stack[1] > 0 then 
   ExecuteFromCFGNode_s6(s5, gas - 1)
  else
     ExecuteFromCFGNode_s5(s5, gas - 1)
}

/** Node 5
* Segment Id for this node is: 5
* Starting at 0x36
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x36 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 1

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  var s2 := PushN(s1, 1, 0x00);
  var s3 := Dup(s2, 1);
   var s4 := Revert(s3);
  s4
}

/** Node 6
* Segment Id for this node is: 10
* Starting at 0x64
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 5
* Net Stack Effect: +4
* Net Capacity Effect: 4
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x64 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 1

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  var s2 := PushN(s1, 2, 0x0077);
  assert s2.stack[0] == 0x77;
  var s3 := PushN(s2, 2, 0x0072);
  assert s3.stack[0] == 0x72;
  assert s3.stack[1] == 0x77;
  var s4 := CallDataSize(s3);
  assert s4.stack[1] == 0x72;
  assert s4.stack[2] == 0x77;
  var s5 := PushN(s4, 1, 0x04);
  assert s5.stack[2] == 0x72;
  assert s5.stack[3] == 0x77;
  var s6 := PushN(s5, 2, 0x020b);
  assert s6.stack[0] == 0x20b;
  assert s6.stack[3] == 0x72;
  assert s6.stack[4] == 0x77;
   var s7 := Jump(s6);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s7(s7, gas - 1)
}

/** Node 7
* Segment Id for this node is: 46
* Starting at 0x20b
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 4
* Net Stack Effect: +1
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x20b as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 5

  requires s0.stack[2] == 0x72

  requires s0.stack[3] == 0x77

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[2] == 0x72;
  assert s1.stack[3] == 0x77;
  var s2 := PushN(s1, 1, 0x00);
  assert s2.stack[3] == 0x72;
  assert s2.stack[4] == 0x77;
  var s3 := PushN(s2, 1, 0x20);
  assert s3.stack[4] == 0x72;
  assert s3.stack[5] == 0x77;
  var s4 := Dup(s3, 3);
  assert s4.stack[5] == 0x72;
  assert s4.stack[6] == 0x77;
  var s5 := Dup(s4, 5);
  assert s5.stack[6] == 0x72;
  assert s5.stack[7] == 0x77;
  var s6 := Sub(s5);
  assert s6.stack[5] == 0x72;
  assert s6.stack[6] == 0x77;
  var s7 := Slt(s6);
  assert s7.stack[4] == 0x72;
  assert s7.stack[5] == 0x77;
  var s8 := IsZero(s7);
  assert s8.stack[4] == 0x72;
  assert s8.stack[5] == 0x77;
  var s9 := PushN(s8, 2, 0x021d);
  assert s9.stack[0] == 0x21d;
  assert s9.stack[5] == 0x72;
  assert s9.stack[6] == 0x77;
   var s10 := JumpI(s9);
  if s9.stack[1] > 0 then 
   ExecuteFromCFGNode_s9(s10, gas - 1)
  else
     ExecuteFromCFGNode_s8(s10, gas - 1)
}

/** Node 8
* Segment Id for this node is: 47
* Starting at 0x219
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x219 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 6

  requires s0.stack[3] == 0x72

  requires s0.stack[4] == 0x77

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x00);
  assert s1.stack[4] == 0x72;
  assert s1.stack[5] == 0x77;
  var s2 := Dup(s1, 1);
  assert s2.stack[5] == 0x72;
  assert s2.stack[6] == 0x77;
   var s3 := Revert(s2);
  s3
}

/** Node 9
* Segment Id for this node is: 48
* Starting at 0x21d
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 4
* Minimum capacity for this segment to prevent stack overflow: 0
* Net Stack Effect: -3
* Net Capacity Effect: +-3
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x21d as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 6

  requires s0.stack[3] == 0x72

  requires s0.stack[4] == 0x77

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[3] == 0x72;
  assert s1.stack[4] == 0x77;
  var s2 := Pop(s1);
  assert s2.stack[2] == 0x72;
  assert s2.stack[3] == 0x77;
  var s3 := CallDataLoad(s2);
  assert s3.stack[2] == 0x72;
  assert s3.stack[3] == 0x77;
  var s4 := Swap(s3, 2);
  assert s4.stack[0] == 0x72;
  assert s4.stack[3] == 0x77;
  var s5 := Swap(s4, 1);
  assert s5.stack[1] == 0x72;
  assert s5.stack[3] == 0x77;
  var s6 := Pop(s5);
  assert s6.stack[0] == 0x72;
  assert s6.stack[2] == 0x77;
   var s7 := Jump(s6);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s10(s7, gas - 1)
}

/** Node 10
* Segment Id for this node is: 11
* Starting at 0x72
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 1
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x72 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 3

  requires s0.stack[1] == 0x77

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[1] == 0x77;
  var s2 := PushN(s1, 2, 0x0124);
  assert s2.stack[0] == 0x124;
  assert s2.stack[2] == 0x77;
   var s3 := Jump(s2);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s11(s3, gas - 1)
}

/** Node 11
* Segment Id for this node is: 26
* Starting at 0x124
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 3
* Net Stack Effect: +1
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x124 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 3

  requires s0.stack[1] == 0x77

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[1] == 0x77;
  var s2 := PushN(s1, 1, 0x00);
  assert s2.stack[2] == 0x77;
  var s3 := PushN(s2, 1, 0x02);
  assert s3.stack[3] == 0x77;
  var s4 := Dup(s3, 3);
  assert s4.stack[4] == 0x77;
  var s5 := Lt(s4);
  assert s5.stack[3] == 0x77;
  var s6 := IsZero(s5);
  assert s6.stack[3] == 0x77;
  var s7 := PushN(s6, 2, 0x0133);
  assert s7.stack[0] == 0x133;
  assert s7.stack[4] == 0x77;
   var s8 := JumpI(s7);
  if s7.stack[1] > 0 then 
   ExecuteFromCFGNode_s15(s8, gas - 1)
  else
     ExecuteFromCFGNode_s12(s8, gas - 1)
}

/** Node 12
* Segment Id for this node is: 27
* Starting at 0x130
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 3
* Minimum capacity for this segment to prevent stack overflow: 0
* Net Stack Effect: -2
* Net Capacity Effect: +-2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x130 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 4

  requires s0.stack[2] == 0x77

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := Pop(s0);
  assert s1.stack[1] == 0x77;
  var s2 := Swap(s1, 1);
  assert s2.stack[0] == 0x77;
   var s3 := Jump(s2);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s13(s3, gas - 1)
}

/** Node 13
* Segment Id for this node is: 12
* Starting at 0x77
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x77 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 2

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  var s2 := PushN(s1, 1, 0x40);
  var s3 := MLoad(s2);
  var s4 := Swap(s3, 1);
  var s5 := Dup(s4, 2);
  var s6 := MStore(s5);
  var s7 := PushN(s6, 1, 0x20);
  var s8 := Add(s7);
  var s9 := PushN(s8, 2, 0x005b);
  assert s9.stack[0] == 0x5b;
   var s10 := Jump(s9);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s14(s10, gas - 1)
}

/** Node 14
* Segment Id for this node is: 9
* Starting at 0x5b
* Segment type is: RETURN Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: -1
* Net Capacity Effect: +-1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x5b as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 2

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  var s2 := PushN(s1, 1, 0x40);
  var s3 := MLoad(s2);
  var s4 := Dup(s3, 1);
  var s5 := Swap(s4, 2);
  var s6 := Sub(s5);
  var s7 := Swap(s6, 1);
   var s8 := Return(s7);
  s8
}

/** Node 15
* Segment Id for this node is: 28
* Starting at 0x133
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 3
* Net Stack Effect: +2
* Net Capacity Effect: 2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x133 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 4

  requires s0.stack[2] == 0x77

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[2] == 0x77;
  var s2 := PushN(s1, 2, 0x013f);
  assert s2.stack[0] == 0x13f;
  assert s2.stack[3] == 0x77;
  var s3 := PushN(s2, 1, 0x02);
  assert s3.stack[1] == 0x13f;
  assert s3.stack[4] == 0x77;
  var s4 := Dup(s3, 4);
  assert s4.stack[2] == 0x13f;
  assert s4.stack[5] == 0x77;
  var s5 := Sub(s4);
  assert s5.stack[1] == 0x13f;
  assert s5.stack[4] == 0x77;
  var s6 := PushN(s5, 2, 0x0124);
  assert s6.stack[0] == 0x124;
  assert s6.stack[2] == 0x13f;
  assert s6.stack[5] == 0x77;
   var s7 := Jump(s6);
  assert s7.stack[4] == 0x77;
//   assert s6.stack[1] == 0x77; 
//   s7
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s11(s7, gas - 1)
}

/** Node 16
* Segment Id for this node is: 6
* Starting at 0x3b
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 5
* Net Stack Effect: +4
* Net Capacity Effect: 4
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x3b as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 1

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  var s2 := PushN(s1, 2, 0x004e);
  assert s2.stack[0] == 0x4e;
  var s3 := PushN(s2, 2, 0x0049);
  assert s3.stack[0] == 0x49;
  assert s3.stack[1] == 0x4e;
  var s4 := CallDataSize(s3);
  assert s4.stack[1] == 0x49;
  assert s4.stack[2] == 0x4e;
  var s5 := PushN(s4, 1, 0x04);
  assert s5.stack[2] == 0x49;
  assert s5.stack[3] == 0x4e;
  var s6 := PushN(s5, 2, 0x0152);
  assert s6.stack[0] == 0x152;
  assert s6.stack[3] == 0x49;
  assert s6.stack[4] == 0x4e;
   var s7 := Jump(s6);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s17(s7, gas - 1)
}

/** Node 17
* Segment Id for this node is: 31
* Starting at 0x152
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 5
* Net Stack Effect: +2
* Net Capacity Effect: 2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x152 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 5

  requires s0.stack[2] == 0x49

  requires s0.stack[3] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[2] == 0x49;
  assert s1.stack[3] == 0x4e;
  var s2 := PushN(s1, 1, 0x00);
  assert s2.stack[3] == 0x49;
  assert s2.stack[4] == 0x4e;
  var s3 := Dup(s2, 1);
  assert s3.stack[4] == 0x49;
  assert s3.stack[5] == 0x4e;
  var s4 := PushN(s3, 1, 0x20);
  assert s4.stack[5] == 0x49;
  assert s4.stack[6] == 0x4e;
  var s5 := Dup(s4, 4);
  assert s5.stack[6] == 0x49;
  assert s5.stack[7] == 0x4e;
  var s6 := Dup(s5, 6);
  assert s6.stack[7] == 0x49;
  assert s6.stack[8] == 0x4e;
  var s7 := Sub(s6);
  assert s7.stack[6] == 0x49;
  assert s7.stack[7] == 0x4e;
  var s8 := Slt(s7);
  assert s8.stack[5] == 0x49;
  assert s8.stack[6] == 0x4e;
  var s9 := IsZero(s8);
  assert s9.stack[5] == 0x49;
  assert s9.stack[6] == 0x4e;
  var s10 := PushN(s9, 2, 0x0165);
  assert s10.stack[0] == 0x165;
  assert s10.stack[6] == 0x49;
  assert s10.stack[7] == 0x4e;
   var s11 := JumpI(s10);
  if s10.stack[1] > 0 then 
   ExecuteFromCFGNode_s19(s11, gas - 1)
  else
     ExecuteFromCFGNode_s18(s11, gas - 1)
}

/** Node 18
* Segment Id for this node is: 32
* Starting at 0x161
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x161 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 7

  requires s0.stack[4] == 0x49

  requires s0.stack[5] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x00);
  assert s1.stack[5] == 0x49;
  assert s1.stack[6] == 0x4e;
  var s2 := Dup(s1, 1);
  assert s2.stack[6] == 0x49;
  assert s2.stack[7] == 0x4e;
   var s3 := Revert(s2);
  s3
}

/** Node 19
* Segment Id for this node is: 33
* Starting at 0x165
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 3
* Minimum capacity for this segment to prevent stack overflow: 4
* Net Stack Effect: +2
* Net Capacity Effect: 2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x165 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 7

  requires s0.stack[4] == 0x49

  requires s0.stack[5] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[4] == 0x49;
  assert s1.stack[5] == 0x4e;
  var s2 := Dup(s1, 3);
  assert s2.stack[5] == 0x49;
  assert s2.stack[6] == 0x4e;
  var s3 := CallDataLoad(s2);
  assert s3.stack[5] == 0x49;
  assert s3.stack[6] == 0x4e;
  var s4 := PushN(s3, 8, 0xffffffffffffffff);
  assert s4.stack[6] == 0x49;
  assert s4.stack[7] == 0x4e;
  var s5 := Dup(s4, 1);
  assert s5.stack[7] == 0x49;
  assert s5.stack[8] == 0x4e;
  var s6 := Dup(s5, 3);
  assert s6.stack[8] == 0x49;
  assert s6.stack[9] == 0x4e;
  var s7 := Gt(s6);
  assert s7.stack[7] == 0x49;
  assert s7.stack[8] == 0x4e;
  var s8 := IsZero(s7);
  assert s8.stack[7] == 0x49;
  assert s8.stack[8] == 0x4e;
  var s9 := PushN(s8, 2, 0x017d);
  assert s9.stack[0] == 0x17d;
  assert s9.stack[8] == 0x49;
  assert s9.stack[9] == 0x4e;
   var s10 := JumpI(s9);
  if s9.stack[1] > 0 then 
   ExecuteFromCFGNode_s21(s10, gas - 1)
  else
     ExecuteFromCFGNode_s20(s10, gas - 1)
}

/** Node 20
* Segment Id for this node is: 34
* Starting at 0x179
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x179 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 9

  requires s0.stack[6] == 0x49

  requires s0.stack[7] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x00);
  assert s1.stack[7] == 0x49;
  assert s1.stack[8] == 0x4e;
  var s2 := Dup(s1, 1);
  assert s2.stack[8] == 0x49;
  assert s2.stack[9] == 0x4e;
   var s3 := Revert(s2);
  s3
}

/** Node 21
* Segment Id for this node is: 35
* Starting at 0x17d
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 6
* Minimum capacity for this segment to prevent stack overflow: 3
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x17d as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 9

  requires s0.stack[6] == 0x49

  requires s0.stack[7] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[6] == 0x49;
  assert s1.stack[7] == 0x4e;
  var s2 := Dup(s1, 2);
  assert s2.stack[7] == 0x49;
  assert s2.stack[8] == 0x4e;
  var s3 := Dup(s2, 6);
  assert s3.stack[8] == 0x49;
  assert s3.stack[9] == 0x4e;
  var s4 := Add(s3);
  assert s4.stack[7] == 0x49;
  assert s4.stack[8] == 0x4e;
  var s5 := Swap(s4, 2);
  assert s5.stack[7] == 0x49;
  assert s5.stack[8] == 0x4e;
  var s6 := Pop(s5);
  assert s6.stack[6] == 0x49;
  assert s6.stack[7] == 0x4e;
  var s7 := Dup(s6, 6);
  assert s7.stack[7] == 0x49;
  assert s7.stack[8] == 0x4e;
  var s8 := PushN(s7, 1, 0x1f);
  assert s8.stack[8] == 0x49;
  assert s8.stack[9] == 0x4e;
  var s9 := Dup(s8, 4);
  assert s9.stack[9] == 0x49;
  assert s9.stack[10] == 0x4e;
  var s10 := Add(s9);
  assert s10.stack[8] == 0x49;
  assert s10.stack[9] == 0x4e;
  var s11 := Slt(s10);
  assert s11.stack[7] == 0x49;
  assert s11.stack[8] == 0x4e;
  var s12 := PushN(s11, 2, 0x0191);
  assert s12.stack[0] == 0x191;
  assert s12.stack[8] == 0x49;
  assert s12.stack[9] == 0x4e;
   var s13 := JumpI(s12);
  if s12.stack[1] > 0 then 
   ExecuteFromCFGNode_s23(s13, gas - 1)
  else
     ExecuteFromCFGNode_s22(s13, gas - 1)
}

/** Node 22
* Segment Id for this node is: 36
* Starting at 0x18d
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x18d as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 9

  requires s0.stack[6] == 0x49

  requires s0.stack[7] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x00);
  assert s1.stack[7] == 0x49;
  assert s1.stack[8] == 0x4e;
  var s2 := Dup(s1, 1);
  assert s2.stack[8] == 0x49;
  assert s2.stack[9] == 0x4e;
   var s3 := Revert(s2);
  s3
}

/** Node 23
* Segment Id for this node is: 37
* Starting at 0x191
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 3
* Net Stack Effect: +1
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x191 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 9

  requires s0.stack[6] == 0x49

  requires s0.stack[7] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[6] == 0x49;
  assert s1.stack[7] == 0x4e;
  var s2 := Dup(s1, 2);
  assert s2.stack[7] == 0x49;
  assert s2.stack[8] == 0x4e;
  var s3 := CallDataLoad(s2);
  assert s3.stack[7] == 0x49;
  assert s3.stack[8] == 0x4e;
  var s4 := Dup(s3, 2);
  assert s4.stack[8] == 0x49;
  assert s4.stack[9] == 0x4e;
  var s5 := Dup(s4, 2);
  assert s5.stack[9] == 0x49;
  assert s5.stack[10] == 0x4e;
  var s6 := Gt(s5);
  assert s6.stack[8] == 0x49;
  assert s6.stack[9] == 0x4e;
  var s7 := IsZero(s6);
  assert s7.stack[8] == 0x49;
  assert s7.stack[9] == 0x4e;
  var s8 := PushN(s7, 2, 0x01a0);
  assert s8.stack[0] == 0x1a0;
  assert s8.stack[9] == 0x49;
  assert s8.stack[10] == 0x4e;
   var s9 := JumpI(s8);
  if s8.stack[1] > 0 then 
   ExecuteFromCFGNode_s25(s9, gas - 1)
  else
     ExecuteFromCFGNode_s24(s9, gas - 1)
}

/** Node 24
* Segment Id for this node is: 38
* Starting at 0x19c
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x19c as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[7] == 0x49

  requires s0.stack[8] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x00);
  assert s1.stack[8] == 0x49;
  assert s1.stack[9] == 0x4e;
  var s2 := Dup(s1, 1);
  assert s2.stack[9] == 0x49;
  assert s2.stack[10] == 0x4e;
   var s3 := Revert(s2);
  s3
}

/** Node 25
* Segment Id for this node is: 39
* Starting at 0x1a0
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 7
* Minimum capacity for this segment to prevent stack overflow: 4
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x1a0 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[7] == 0x49

  requires s0.stack[8] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[7] == 0x49;
  assert s1.stack[8] == 0x4e;
  var s2 := Dup(s1, 7);
  assert s2.stack[8] == 0x49;
  assert s2.stack[9] == 0x4e;
  var s3 := PushN(s2, 1, 0x20);
  assert s3.stack[9] == 0x49;
  assert s3.stack[10] == 0x4e;
  var s4 := Dup(s3, 3);
  assert s4.stack[10] == 0x49;
  assert s4.stack[11] == 0x4e;
  var s5 := PushN(s4, 1, 0x05);
  assert s5.stack[11] == 0x49;
  assert s5.stack[12] == 0x4e;
  var s6 := Shl(s5);
  assert s6.stack[10] == 0x49;
  assert s6.stack[11] == 0x4e;
  var s7 := Dup(s6, 6);
  assert s7.stack[11] == 0x49;
  assert s7.stack[12] == 0x4e;
  var s8 := Add(s7);
  assert s8.stack[10] == 0x49;
  assert s8.stack[11] == 0x4e;
  var s9 := Add(s8);
  assert s9.stack[9] == 0x49;
  assert s9.stack[10] == 0x4e;
  var s10 := Gt(s9);
  assert s10.stack[8] == 0x49;
  assert s10.stack[9] == 0x4e;
  var s11 := IsZero(s10);
  assert s11.stack[8] == 0x49;
  assert s11.stack[9] == 0x4e;
  var s12 := PushN(s11, 2, 0x01b5);
  assert s12.stack[0] == 0x1b5;
  assert s12.stack[9] == 0x49;
  assert s12.stack[10] == 0x4e;
   var s13 := JumpI(s12);
  if s12.stack[1] > 0 then 
   ExecuteFromCFGNode_s27(s13, gas - 1)
  else
     ExecuteFromCFGNode_s26(s13, gas - 1)
}

/** Node 26
* Segment Id for this node is: 40
* Starting at 0x1b1
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x1b1 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[7] == 0x49

  requires s0.stack[8] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 1, 0x00);
  assert s1.stack[8] == 0x49;
  assert s1.stack[9] == 0x4e;
  var s2 := Dup(s1, 1);
  assert s2.stack[9] == 0x49;
  assert s2.stack[10] == 0x4e;
   var s3 := Revert(s2);
  s3
}

/** Node 27
* Segment Id for this node is: 41
* Starting at 0x1b5
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 8
* Minimum capacity for this segment to prevent stack overflow: 1
* Net Stack Effect: -6
* Net Capacity Effect: +-6
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x1b5 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[7] == 0x49

  requires s0.stack[8] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[7] == 0x49;
  assert s1.stack[8] == 0x4e;
  var s2 := PushN(s1, 1, 0x20);
  assert s2.stack[8] == 0x49;
  assert s2.stack[9] == 0x4e;
  var s3 := Swap(s2, 3);
  assert s3.stack[8] == 0x49;
  assert s3.stack[9] == 0x4e;
  var s4 := Swap(s3, 1);
  assert s4.stack[8] == 0x49;
  assert s4.stack[9] == 0x4e;
  var s5 := Swap(s4, 3);
  assert s5.stack[8] == 0x49;
  assert s5.stack[9] == 0x4e;
  var s6 := Add(s5);
  assert s6.stack[7] == 0x49;
  assert s6.stack[8] == 0x4e;
  var s7 := Swap(s6, 7);
  assert s7.stack[0] == 0x49;
  assert s7.stack[8] == 0x4e;
  var s8 := Swap(s7, 2);
  assert s8.stack[2] == 0x49;
  assert s8.stack[8] == 0x4e;
  var s9 := Swap(s8, 6);
  assert s9.stack[2] == 0x49;
  assert s9.stack[8] == 0x4e;
  var s10 := Pop(s9);
  assert s10.stack[1] == 0x49;
  assert s10.stack[7] == 0x4e;
  var s11 := Swap(s10, 1);
  assert s11.stack[0] == 0x49;
  assert s11.stack[7] == 0x4e;
  var s12 := Swap(s11, 4);
  assert s12.stack[4] == 0x49;
  assert s12.stack[7] == 0x4e;
  var s13 := Pop(s12);
  assert s13.stack[3] == 0x49;
  assert s13.stack[6] == 0x4e;
  var s14 := Pop(s13);
  assert s14.stack[2] == 0x49;
  assert s14.stack[5] == 0x4e;
  var s15 := Pop(s14);
  assert s15.stack[1] == 0x49;
  assert s15.stack[4] == 0x4e;
  var s16 := Pop(s15);
  assert s16.stack[0] == 0x49;
  assert s16.stack[3] == 0x4e;
   var s17 := Jump(s16);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s28(s17, gas - 1)
}

/** Node 28
* Segment Id for this node is: 7
* Starting at 0x49
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 1
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x49 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 4

  requires s0.stack[2] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[2] == 0x4e;
  var s2 := PushN(s1, 2, 0x0085);
  assert s2.stack[0] == 0x85;
  assert s2.stack[3] == 0x4e;
   var s3 := Jump(s2);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s29(s3, gas - 1)
}

/** Node 29
* Segment Id for this node is: 13
* Starting at 0x85
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 4
* Net Stack Effect: +2
* Net Capacity Effect: 2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x85 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 4

  requires s0.stack[2] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[2] == 0x4e;
  var s2 := PushN(s1, 1, 0x60);
  assert s2.stack[3] == 0x4e;
  var s3 := Dup(s2, 2);
  assert s3.stack[4] == 0x4e;
  var s4 := PushN(s3, 8, 0xffffffffffffffff);
  assert s4.stack[5] == 0x4e;
  var s5 := Dup(s4, 2);
  assert s5.stack[6] == 0x4e;
  var s6 := Gt(s5);
  assert s6.stack[5] == 0x4e;
  var s7 := IsZero(s6);
  assert s7.stack[5] == 0x4e;
  var s8 := PushN(s7, 2, 0x00a0);
  assert s8.stack[0] == 0xa0;
  assert s8.stack[6] == 0x4e;
   var s9 := JumpI(s8);
  if s8.stack[1] > 0 then 
   ExecuteFromCFGNode_s32(s9, gas - 1)
  else
     ExecuteFromCFGNode_s30(s9, gas - 1)
}

/** Node 30
* Segment Id for this node is: 14
* Starting at 0x99
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +1
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x99 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 6

  requires s0.stack[4] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 2, 0x00a0);
  assert s1.stack[0] == 0xa0;
  assert s1.stack[5] == 0x4e;
  var s2 := PushN(s1, 2, 0x0224);
  assert s2.stack[0] == 0x224;
  assert s2.stack[1] == 0xa0;
  assert s2.stack[6] == 0x4e;
   var s3 := Jump(s2);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s31(s3, gas - 1)
}

/** Node 31
* Segment Id for this node is: 49
* Starting at 0x224
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x224 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 7

  requires s0.stack[0] == 0xa0

  requires s0.stack[5] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[0] == 0xa0;
  assert s1.stack[5] == 0x4e;
  var s2 := PushN(s1, 4, 0x4e487b71);
  assert s2.stack[1] == 0xa0;
  assert s2.stack[6] == 0x4e;
  var s3 := PushN(s2, 1, 0xe0);
  assert s3.stack[2] == 0xa0;
  assert s3.stack[7] == 0x4e;
  var s4 := Shl(s3);
  assert s4.stack[1] == 0xa0;
  assert s4.stack[6] == 0x4e;
  var s5 := PushN(s4, 1, 0x00);
  assert s5.stack[2] == 0xa0;
  assert s5.stack[7] == 0x4e;
  var s6 := MStore(s5);
  assert s6.stack[0] == 0xa0;
  assert s6.stack[5] == 0x4e;
  var s7 := PushN(s6, 1, 0x41);
  assert s7.stack[1] == 0xa0;
  assert s7.stack[6] == 0x4e;
  var s8 := PushN(s7, 1, 0x04);
  assert s8.stack[2] == 0xa0;
  assert s8.stack[7] == 0x4e;
  var s9 := MStore(s8);
  assert s9.stack[0] == 0xa0;
  assert s9.stack[5] == 0x4e;
  var s10 := PushN(s9, 1, 0x24);
  assert s10.stack[1] == 0xa0;
  assert s10.stack[6] == 0x4e;
  var s11 := PushN(s10, 1, 0x00);
  assert s11.stack[2] == 0xa0;
  assert s11.stack[7] == 0x4e;
   var s12 := Revert(s11);
  s12
}

/** Node 32
* Segment Id for this node is: 15
* Starting at 0xa0
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 3
* Net Stack Effect: +1
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xa0 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 6

  requires s0.stack[4] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[4] == 0x4e;
  var s2 := PushN(s1, 1, 0x40);
  assert s2.stack[5] == 0x4e;
  var s3 := MLoad(s2);
  assert s3.stack[5] == 0x4e;
  var s4 := Swap(s3, 1);
  assert s4.stack[5] == 0x4e;
  var s5 := Dup(s4, 1);
  assert s5.stack[6] == 0x4e;
  var s6 := Dup(s5, 3);
  assert s6.stack[7] == 0x4e;
  var s7 := MStore(s6);
  assert s7.stack[5] == 0x4e;
  var s8 := Dup(s7, 1);
  assert s8.stack[6] == 0x4e;
  var s9 := PushN(s8, 1, 0x20);
  assert s9.stack[7] == 0x4e;
  var s10 := Mul(s9);
  assert s10.stack[6] == 0x4e;
  var s11 := PushN(s10, 1, 0x20);
  assert s11.stack[7] == 0x4e;
  var s12 := Add(s11);
  assert s12.stack[6] == 0x4e;
  var s13 := Dup(s12, 3);
  assert s13.stack[7] == 0x4e;
  var s14 := Add(s13);
  assert s14.stack[6] == 0x4e;
  var s15 := PushN(s14, 1, 0x40);
  assert s15.stack[7] == 0x4e;
  var s16 := MStore(s15);
  assert s16.stack[5] == 0x4e;
  var s17 := Dup(s16, 1);
  assert s17.stack[6] == 0x4e;
  var s18 := IsZero(s17);
  assert s18.stack[6] == 0x4e;
  var s19 := PushN(s18, 2, 0x00c9);
  assert s19.stack[0] == 0xc9;
  assert s19.stack[7] == 0x4e;
   var s20 := JumpI(s19);
  if s19.stack[1] > 0 then 
   ExecuteFromCFGNode_s34(s20, gas - 1)
  else
     ExecuteFromCFGNode_s33(s20, gas - 1)
}

/** Node 33
* Segment Id for this node is: 16
* Starting at 0xba
* Segment type is: CONT Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 5
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xba as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 7

  requires s0.stack[5] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := Dup(s0, 2);
  assert s1.stack[6] == 0x4e;
  var s2 := PushN(s1, 1, 0x20);
  assert s2.stack[7] == 0x4e;
  var s3 := Add(s2);
  assert s3.stack[6] == 0x4e;
  var s4 := PushN(s3, 1, 0x20);
  assert s4.stack[7] == 0x4e;
  var s5 := Dup(s4, 3);
  assert s5.stack[8] == 0x4e;
  var s6 := Mul(s5);
  assert s6.stack[7] == 0x4e;
  var s7 := Dup(s6, 1);
  assert s7.stack[8] == 0x4e;
  var s8 := CallDataSize(s7);
  assert s8.stack[9] == 0x4e;
  var s9 := Dup(s8, 4);
  assert s9.stack[10] == 0x4e;
  var s10 := CallDataCopy(s9);
  assert s10.stack[7] == 0x4e;
  var s11 := Add(s10);
  assert s11.stack[6] == 0x4e;
  var s12 := Swap(s11, 1);
  assert s12.stack[6] == 0x4e;
   var s13 := Pop(s12);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s34(s13, gas - 1)
}

/** Node 34
* Segment Id for this node is: 17
* Starting at 0xc9
* Segment type is: CONT Segment
* Minimum stack size for this segment to prevent stack underflow: 3
* Minimum capacity for this segment to prevent stack overflow: 0
* Net Stack Effect: -1
* Net Capacity Effect: +-1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xc9 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 7

  requires s0.stack[5] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[5] == 0x4e;
  var s2 := Pop(s1);
  assert s2.stack[4] == 0x4e;
  var s3 := Swap(s2, 1);
  assert s3.stack[4] == 0x4e;
  var s4 := Pop(s3);
  assert s4.stack[3] == 0x4e;
   var s5 := PushN(s4, 1, 0x00);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s35(s5, gas - 1)
}

/** Node 35
* Segment Id for this node is: 18
* Starting at 0xcf
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 3
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xcf as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 6

  requires s0.stack[4] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[4] == 0x4e;
  var s2 := Dup(s1, 3);
  assert s2.stack[5] == 0x4e;
  var s3 := Dup(s2, 2);
  assert s3.stack[6] == 0x4e;
  var s4 := Lt(s3);
  assert s4.stack[5] == 0x4e;
  var s5 := IsZero(s4);
  assert s5.stack[5] == 0x4e;
  var s6 := PushN(s5, 2, 0x011d);
  assert s6.stack[0] == 0x11d;
  assert s6.stack[6] == 0x4e;
   var s7 := JumpI(s6);
  if s6.stack[1] > 0 then 
   ExecuteFromCFGNode_s47(s7, gas - 1)
  else
     ExecuteFromCFGNode_s36(s7, gas - 1)
}

/** Node 36
* Segment Id for this node is: 19
* Starting at 0xd8
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 4
* Minimum capacity for this segment to prevent stack overflow: 6
* Net Stack Effect: +4
* Net Capacity Effect: 4
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xd8 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 6

  requires s0.stack[4] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 2, 0x00f8);
  assert s1.stack[0] == 0xf8;
  assert s1.stack[5] == 0x4e;
  var s2 := Dup(s1, 5);
  assert s2.stack[1] == 0xf8;
  assert s2.stack[6] == 0x4e;
  var s3 := Dup(s2, 5);
  assert s3.stack[2] == 0xf8;
  assert s3.stack[7] == 0x4e;
  var s4 := Dup(s3, 4);
  assert s4.stack[3] == 0xf8;
  assert s4.stack[8] == 0x4e;
  var s5 := Dup(s4, 2);
  assert s5.stack[4] == 0xf8;
  assert s5.stack[9] == 0x4e;
  var s6 := Dup(s5, 2);
  assert s6.stack[5] == 0xf8;
  assert s6.stack[10] == 0x4e;
  var s7 := Lt(s6);
  assert s7.stack[4] == 0xf8;
  assert s7.stack[9] == 0x4e;
  var s8 := PushN(s7, 2, 0x00ec);
  assert s8.stack[0] == 0xec;
  assert s8.stack[5] == 0xf8;
  assert s8.stack[10] == 0x4e;
   var s9 := JumpI(s8);
  if s8.stack[1] > 0 then 
   ExecuteFromCFGNode_s39(s9, gas - 1)
  else
     ExecuteFromCFGNode_s37(s9, gas - 1)
}

/** Node 37
* Segment Id for this node is: 20
* Starting at 0xe5
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +1
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xe5 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[3] == 0xf8

  requires s0.stack[8] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 2, 0x00ec);
  assert s1.stack[0] == 0xec;
  assert s1.stack[4] == 0xf8;
  assert s1.stack[9] == 0x4e;
  var s2 := PushN(s1, 2, 0x023a);
  assert s2.stack[0] == 0x23a;
  assert s2.stack[1] == 0xec;
  assert s2.stack[5] == 0xf8;
  assert s2.stack[10] == 0x4e;
   var s3 := Jump(s2);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s38(s3, gas - 1)
}

/** Node 38
* Segment Id for this node is: 50
* Starting at 0x23a
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x23a as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 11

  requires s0.stack[0] == 0xec

  requires s0.stack[4] == 0xf8

  requires s0.stack[9] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[0] == 0xec;
  assert s1.stack[4] == 0xf8;
  assert s1.stack[9] == 0x4e;
  var s2 := PushN(s1, 4, 0x4e487b71);
  assert s2.stack[1] == 0xec;
  assert s2.stack[5] == 0xf8;
  assert s2.stack[10] == 0x4e;
  var s3 := PushN(s2, 1, 0xe0);
  assert s3.stack[2] == 0xec;
  assert s3.stack[6] == 0xf8;
  assert s3.stack[11] == 0x4e;
  var s4 := Shl(s3);
  assert s4.stack[1] == 0xec;
  assert s4.stack[5] == 0xf8;
  assert s4.stack[10] == 0x4e;
  var s5 := PushN(s4, 1, 0x00);
  assert s5.stack[2] == 0xec;
  assert s5.stack[6] == 0xf8;
  assert s5.stack[11] == 0x4e;
  var s6 := MStore(s5);
  assert s6.stack[0] == 0xec;
  assert s6.stack[4] == 0xf8;
  assert s6.stack[9] == 0x4e;
  var s7 := PushN(s6, 1, 0x32);
  assert s7.stack[1] == 0xec;
  assert s7.stack[5] == 0xf8;
  assert s7.stack[10] == 0x4e;
  var s8 := PushN(s7, 1, 0x04);
  assert s8.stack[2] == 0xec;
  assert s8.stack[6] == 0xf8;
  assert s8.stack[11] == 0x4e;
  var s9 := MStore(s8);
  assert s9.stack[0] == 0xec;
  assert s9.stack[4] == 0xf8;
  assert s9.stack[9] == 0x4e;
  var s10 := PushN(s9, 1, 0x24);
  assert s10.stack[1] == 0xec;
  assert s10.stack[5] == 0xf8;
  assert s10.stack[10] == 0x4e;
  var s11 := PushN(s10, 1, 0x00);
  assert s11.stack[2] == 0xec;
  assert s11.stack[6] == 0xf8;
  assert s11.stack[11] == 0x4e;
   var s12 := Revert(s11);
  s12
}

/** Node 39
* Segment Id for this node is: 21
* Starting at 0xec
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 3
* Minimum capacity for this segment to prevent stack overflow: 0
* Net Stack Effect: -2
* Net Capacity Effect: +-2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xec as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[3] == 0xf8

  requires s0.stack[8] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[3] == 0xf8;
  assert s1.stack[8] == 0x4e;
  var s2 := Swap(s1, 1);
  assert s2.stack[3] == 0xf8;
  assert s2.stack[8] == 0x4e;
  var s3 := Pop(s2);
  assert s3.stack[2] == 0xf8;
  assert s3.stack[7] == 0x4e;
  var s4 := PushN(s3, 1, 0x20);
  assert s4.stack[3] == 0xf8;
  assert s4.stack[8] == 0x4e;
  var s5 := Mul(s4);
  assert s5.stack[2] == 0xf8;
  assert s5.stack[7] == 0x4e;
  var s6 := Add(s5);
  assert s6.stack[1] == 0xf8;
  assert s6.stack[6] == 0x4e;
  var s7 := CallDataLoad(s6);
  assert s7.stack[1] == 0xf8;
  assert s7.stack[6] == 0x4e;
  var s8 := PushN(s7, 2, 0x0124);
  assert s8.stack[0] == 0x124;
  assert s8.stack[2] == 0xf8;
  assert s8.stack[7] == 0x4e;
   var s9 := Jump(s8);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s40(s9, gas - 1)
}

/** Node 40
* Segment Id for this node is: 26
* Starting at 0x124
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 3
* Net Stack Effect: +1
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x124 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 8

  requires s0.stack[1] == 0xf8

  requires s0.stack[6] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[1] == 0xf8;
  assert s1.stack[6] == 0x4e;
  var s2 := PushN(s1, 1, 0x00);
  assert s2.stack[2] == 0xf8;
  assert s2.stack[7] == 0x4e;
  var s3 := PushN(s2, 1, 0x02);
  assert s3.stack[3] == 0xf8;
  assert s3.stack[8] == 0x4e;
  var s4 := Dup(s3, 3);
  assert s4.stack[4] == 0xf8;
  assert s4.stack[9] == 0x4e;
  var s5 := Lt(s4);
  assert s5.stack[3] == 0xf8;
  assert s5.stack[8] == 0x4e;
  var s6 := IsZero(s5);
  assert s6.stack[3] == 0xf8;
  assert s6.stack[8] == 0x4e;
  var s7 := PushN(s6, 2, 0x0133);
  assert s7.stack[0] == 0x133;
  assert s7.stack[4] == 0xf8;
  assert s7.stack[9] == 0x4e;
   var s8 := JumpI(s7);
  if s7.stack[1] > 0 then 
   ExecuteFromCFGNode_s46(s8, gas - 1)
  else
     ExecuteFromCFGNode_s41(s8, gas - 1)
}

/** Node 41
* Segment Id for this node is: 27
* Starting at 0x130
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 3
* Minimum capacity for this segment to prevent stack overflow: 0
* Net Stack Effect: -2
* Net Capacity Effect: +-2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x130 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 9

  requires s0.stack[2] == 0xf8

  requires s0.stack[7] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := Pop(s0);
  assert s1.stack[1] == 0xf8;
  assert s1.stack[6] == 0x4e;
  var s2 := Swap(s1, 1);
  assert s2.stack[0] == 0xf8;
  assert s2.stack[6] == 0x4e;
   var s3 := Jump(s2);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s42(s3, gas - 1)
}

/** Node 42
* Segment Id for this node is: 22
* Starting at 0xf8
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 3
* Minimum capacity for this segment to prevent stack overflow: 4
* Net Stack Effect: +2
* Net Capacity Effect: 2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0xf8 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 7

  requires s0.stack[5] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[5] == 0x4e;
  var s2 := Dup(s1, 3);
  assert s2.stack[6] == 0x4e;
  var s3 := Dup(s2, 3);
  assert s3.stack[7] == 0x4e;
  var s4 := Dup(s3, 2);
  assert s4.stack[8] == 0x4e;
  var s5 := MLoad(s4);
  assert s5.stack[8] == 0x4e;
  var s6 := Dup(s5, 2);
  assert s6.stack[9] == 0x4e;
  var s7 := Lt(s6);
  assert s7.stack[8] == 0x4e;
  var s8 := PushN(s7, 2, 0x010a);
  assert s8.stack[0] == 0x10a;
  assert s8.stack[9] == 0x4e;
   var s9 := JumpI(s8);
  if s8.stack[1] > 0 then 
   ExecuteFromCFGNode_s45(s9, gas - 1)
  else
     ExecuteFromCFGNode_s43(s9, gas - 1)
}

/** Node 43
* Segment Id for this node is: 23
* Starting at 0x103
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +1
* Net Capacity Effect: 1
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x103 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 9

  requires s0.stack[7] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := PushN(s0, 2, 0x010a);
  assert s1.stack[0] == 0x10a;
  assert s1.stack[8] == 0x4e;
  var s2 := PushN(s1, 2, 0x023a);
  assert s2.stack[0] == 0x23a;
  assert s2.stack[1] == 0x10a;
  assert s2.stack[9] == 0x4e;
   var s3 := Jump(s2);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s44(s3, gas - 1)
}

/** Node 44
* Segment Id for this node is: 50
* Starting at 0x23a
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x23a as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[0] == 0x10a

  requires s0.stack[8] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[0] == 0x10a;
  assert s1.stack[8] == 0x4e;
  var s2 := PushN(s1, 4, 0x4e487b71);
  assert s2.stack[1] == 0x10a;
  assert s2.stack[9] == 0x4e;
  var s3 := PushN(s2, 1, 0xe0);
  assert s3.stack[2] == 0x10a;
  assert s3.stack[10] == 0x4e;
  var s4 := Shl(s3);
  assert s4.stack[1] == 0x10a;
  assert s4.stack[9] == 0x4e;
  var s5 := PushN(s4, 1, 0x00);
  assert s5.stack[2] == 0x10a;
  assert s5.stack[10] == 0x4e;
  var s6 := MStore(s5);
  assert s6.stack[0] == 0x10a;
  assert s6.stack[8] == 0x4e;
  var s7 := PushN(s6, 1, 0x32);
  assert s7.stack[1] == 0x10a;
  assert s7.stack[9] == 0x4e;
  var s8 := PushN(s7, 1, 0x04);
  assert s8.stack[2] == 0x10a;
  assert s8.stack[10] == 0x4e;
  var s9 := MStore(s8);
  assert s9.stack[0] == 0x10a;
  assert s9.stack[8] == 0x4e;
  var s10 := PushN(s9, 1, 0x24);
  assert s10.stack[1] == 0x10a;
  assert s10.stack[9] == 0x4e;
  var s11 := PushN(s10, 1, 0x00);
  assert s11.stack[2] == 0x10a;
  assert s11.stack[10] == 0x4e;
   var s12 := Revert(s11);
  s12
}

/** Node 45
* Segment Id for this node is: 24
* Starting at 0x10a
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 4
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: -3
* Net Capacity Effect: +-3
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x10a as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 9

  requires s0.stack[7] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[7] == 0x4e;
  var s2 := PushN(s1, 1, 0x20);
  assert s2.stack[8] == 0x4e;
  var s3 := Swap(s2, 1);
  assert s3.stack[8] == 0x4e;
  var s4 := Dup(s3, 2);
  assert s4.stack[9] == 0x4e;
  var s5 := Mul(s4);
  assert s5.stack[8] == 0x4e;
  var s6 := Swap(s5, 2);
  assert s6.stack[8] == 0x4e;
  var s7 := Swap(s6, 1);
  assert s7.stack[8] == 0x4e;
  var s8 := Swap(s7, 2);
  assert s8.stack[8] == 0x4e;
  var s9 := Add(s8);
  assert s9.stack[7] == 0x4e;
  var s10 := Add(s9);
  assert s10.stack[6] == 0x4e;
  var s11 := MStore(s10);
  assert s11.stack[4] == 0x4e;
  var s12 := PushN(s11, 1, 0x01);
  assert s12.stack[5] == 0x4e;
  var s13 := Add(s12);
  assert s13.stack[4] == 0x4e;
  var s14 := PushN(s13, 2, 0x00cf);
  assert s14.stack[0] == 0xcf;
  assert s14.stack[5] == 0x4e;
   var s15 := Jump(s14);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s35(s15, gas - 1)
}

/** Node 46
* Segment Id for this node is: 28
* Starting at 0x133
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 3
* Net Stack Effect: +2
* Net Capacity Effect: 2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x133 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 9

  requires s0.stack[2] == 0xf8

  requires s0.stack[7] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[2] == 0xf8;
  assert s1.stack[7] == 0x4e;
  var s2 := PushN(s1, 2, 0x013f);
  assert s2.stack[0] == 0x13f;
  assert s2.stack[3] == 0xf8;
  assert s2.stack[8] == 0x4e;
  var s3 := PushN(s2, 1, 0x02);
  assert s3.stack[1] == 0x13f;
  assert s3.stack[4] == 0xf8;
  assert s3.stack[9] == 0x4e;
  var s4 := Dup(s3, 4);
  assert s4.stack[2] == 0x13f;
  assert s4.stack[5] == 0xf8;
  assert s4.stack[10] == 0x4e;
  var s5 := Sub(s4);
  assert s5.stack[1] == 0x13f;
  assert s5.stack[4] == 0xf8;
  assert s5.stack[9] == 0x4e;
  var s6 := PushN(s5, 2, 0x0124);
  assert s6.stack[0] == 0x124;
  assert s6.stack[2] == 0x13f;
  assert s6.stack[5] == 0xf8;
  assert s6.stack[10] == 0x4e;
   var s7 := Jump(s6);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s40(s7, gas - 1)
}

/** Node 47
* Segment Id for this node is: 25
* Starting at 0x11d
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 5
* Minimum capacity for this segment to prevent stack overflow: 0
* Net Stack Effect: -4
* Net Capacity Effect: +-4
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x11d as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 6

  requires s0.stack[4] == 0x4e

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[4] == 0x4e;
  var s2 := Pop(s1);
  assert s2.stack[3] == 0x4e;
  var s3 := Swap(s2, 3);
  assert s3.stack[0] == 0x4e;
  var s4 := Swap(s3, 2);
  assert s4.stack[2] == 0x4e;
  var s5 := Pop(s4);
  assert s5.stack[1] == 0x4e;
  var s6 := Pop(s5);
  assert s6.stack[0] == 0x4e;
   var s7 := Jump(s6);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s48(s7, gas - 1)
}

/** Node 48
* Segment Id for this node is: 8
* Starting at 0x4e
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 1
* Minimum capacity for this segment to prevent stack overflow: 3
* Net Stack Effect: +2
* Net Capacity Effect: 2
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x4e as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 2

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  var s2 := PushN(s1, 1, 0x40);
  var s3 := MLoad(s2);
  var s4 := PushN(s3, 2, 0x005b);
  assert s4.stack[0] == 0x5b;
  var s5 := Swap(s4, 2);
  assert s5.stack[2] == 0x5b;
  var s6 := Swap(s5, 1);
  assert s6.stack[2] == 0x5b;
  var s7 := PushN(s6, 2, 0x01c7);
  assert s7.stack[0] == 0x1c7;
  assert s7.stack[3] == 0x5b;
   var s8 := Jump(s7);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s49(s8, gas - 1)
}

/** Node 49
* Segment Id for this node is: 42
* Starting at 0x1c7
* Segment type is: CONT Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 6
* Net Stack Effect: +6
* Net Capacity Effect: 6
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x1c7 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 4

  requires s0.stack[2] == 0x5b

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[2] == 0x5b;
  var s2 := PushN(s1, 1, 0x20);
  assert s2.stack[3] == 0x5b;
  var s3 := Dup(s2, 1);
  assert s3.stack[4] == 0x5b;
  var s4 := Dup(s3, 3);
  assert s4.stack[5] == 0x5b;
  var s5 := MStore(s4);
  assert s5.stack[3] == 0x5b;
  var s6 := Dup(s5, 3);
  assert s6.stack[4] == 0x5b;
  var s7 := MLoad(s6);
  assert s7.stack[4] == 0x5b;
  var s8 := Dup(s7, 3);
  assert s8.stack[5] == 0x5b;
  var s9 := Dup(s8, 3);
  assert s9.stack[6] == 0x5b;
  var s10 := Add(s9);
  assert s10.stack[5] == 0x5b;
  var s11 := Dup(s10, 2);
  assert s11.stack[6] == 0x5b;
  var s12 := Swap(s11, 1);
  assert s12.stack[6] == 0x5b;
  var s13 := MStore(s12);
  assert s13.stack[4] == 0x5b;
  var s14 := PushN(s13, 1, 0x00);
  assert s14.stack[5] == 0x5b;
  var s15 := Swap(s14, 2);
  assert s15.stack[5] == 0x5b;
  var s16 := Swap(s15, 1);
  assert s16.stack[5] == 0x5b;
  var s17 := Dup(s16, 5);
  assert s17.stack[6] == 0x5b;
  var s18 := Dup(s17, 3);
  assert s18.stack[7] == 0x5b;
  var s19 := Add(s18);
  assert s19.stack[6] == 0x5b;
  var s20 := Swap(s19, 1);
  assert s20.stack[6] == 0x5b;
  var s21 := PushN(s20, 1, 0x40);
  assert s21.stack[7] == 0x5b;
  var s22 := Dup(s21, 6);
  assert s22.stack[8] == 0x5b;
  var s23 := Add(s22);
  assert s23.stack[7] == 0x5b;
  var s24 := Swap(s23, 1);
  assert s24.stack[7] == 0x5b;
   var s25 := Dup(s24, 5);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s50(s25, gas - 1)
}

/** Node 50
* Segment Id for this node is: 43
* Starting at 0x1e3
* Segment type is: JUMPI Segment
* Minimum stack size for this segment to prevent stack underflow: 2
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x1e3 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[8] == 0x5b

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[8] == 0x5b;
  var s2 := Dup(s1, 2);
  assert s2.stack[9] == 0x5b;
  var s3 := Dup(s2, 2);
  assert s3.stack[10] == 0x5b;
  var s4 := Lt(s3);
  assert s4.stack[9] == 0x5b;
  var s5 := IsZero(s4);
  assert s5.stack[9] == 0x5b;
  var s6 := PushN(s5, 2, 0x01ff);
  assert s6.stack[0] == 0x1ff;
  assert s6.stack[10] == 0x5b;
   var s7 := JumpI(s6);
  if s6.stack[1] > 0 then 
   ExecuteFromCFGNode_s52(s7, gas - 1)
  else
     ExecuteFromCFGNode_s51(s7, gas - 1)
}

/** Node 51
* Segment Id for this node is: 44
* Starting at 0x1ec
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 5
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x1ec as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[8] == 0x5b

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := Dup(s0, 4);
  assert s1.stack[9] == 0x5b;
  var s2 := MLoad(s1);
  assert s2.stack[9] == 0x5b;
  var s3 := Dup(s2, 4);
  assert s3.stack[10] == 0x5b;
  var s4 := MStore(s3);
  assert s4.stack[8] == 0x5b;
  var s5 := Swap(s4, 3);
  assert s5.stack[8] == 0x5b;
  var s6 := Dup(s5, 5);
  assert s6.stack[9] == 0x5b;
  var s7 := Add(s6);
  assert s7.stack[8] == 0x5b;
  var s8 := Swap(s7, 3);
  assert s8.stack[8] == 0x5b;
  var s9 := Swap(s8, 2);
  assert s9.stack[8] == 0x5b;
  var s10 := Dup(s9, 5);
  assert s10.stack[9] == 0x5b;
  var s11 := Add(s10);
  assert s11.stack[8] == 0x5b;
  var s12 := Swap(s11, 2);
  assert s12.stack[8] == 0x5b;
  var s13 := PushN(s12, 1, 0x01);
  assert s13.stack[9] == 0x5b;
  var s14 := Add(s13);
  assert s14.stack[8] == 0x5b;
  var s15 := PushN(s14, 2, 0x01e3);
  assert s15.stack[0] == 0x1e3;
  assert s15.stack[9] == 0x5b;
   var s16 := Jump(s15);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s50(s16, gas - 1)
}

/** Node 52
* Segment Id for this node is: 45
* Starting at 0x1ff
* Segment type is: JUMP Segment
* Minimum stack size for this segment to prevent stack underflow: 9
* Minimum capacity for this segment to prevent stack overflow: 0
* Net Stack Effect: -8
* Net Capacity Effect: +-8
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x1ff as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 10

  requires s0.stack[8] == 0x5b

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  assert s1.stack[8] == 0x5b;
  var s2 := Pop(s1);
  assert s2.stack[7] == 0x5b;
  var s3 := Swap(s2, 1);
  assert s3.stack[7] == 0x5b;
  var s4 := Swap(s3, 7);
  assert s4.stack[0] == 0x5b;
  var s5 := Swap(s4, 6);
  assert s5.stack[6] == 0x5b;
  var s6 := Pop(s5);
  assert s6.stack[5] == 0x5b;
  var s7 := Pop(s6);
  assert s7.stack[4] == 0x5b;
  var s8 := Pop(s7);
  assert s8.stack[3] == 0x5b;
  var s9 := Pop(s8);
  assert s9.stack[2] == 0x5b;
  var s10 := Pop(s9);
  assert s10.stack[1] == 0x5b;
  var s11 := Pop(s10);
  assert s11.stack[0] == 0x5b;
   var s12 := Jump(s11);
  // jump to the successor Next() or Tgt of JUMP;
  ExecuteFromCFGNode_s14(s12, gas - 1)
}

/** Node 53
* Segment Id for this node is: 5
* Starting at 0x36
* Segment type is: STOP Segment
* Minimum stack size for this segment to prevent stack underflow: 0
* Minimum capacity for this segment to prevent stack overflow: 2
* Net Stack Effect: +0
* Net Capacity Effect: +0
*/
function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
  // PC requirement for this node.
  requires s0.pc == 0x36 as nat
  // Stack requirements for this node.
  requires s0.IsValid() 
  requires s0.Operands() >= 0

  decreases gas
{
if gas == 0 then Revert(s0)
else
  var s1 := JumpDest(s0);
  var s2 := PushN(s1, 1, 0x00);
  var s3 := Dup(s2, 1);
   var s4 := Revert(s3);
  s4
}
}
