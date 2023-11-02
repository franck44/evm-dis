
include "../../../../../../evm-dafny/src/dafny/state.dfy"
include "../../../../../../evm-dafny/src/dafny/bytecode.dfy"

module DafnyEVMProofObject {
import opened Int
import EvmState
import opened Bytecode
/** Lemma for Jumpdest */
lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)
 ensures s.IsJumpDest(0x2 as u256)
 ensures s.IsJumpDest(0x13 as u256)


/** Code starting at 0x0 */
function {:opaque} ExecuteFromTag_0(s0: EvmState.ExecutingState): (s': EvmState.State)
  requires s0.PC() == 0x0 as nat
  // Net Operands effect 2
  requires s0.Operands() >= 0
  // Net Capacity effect -2
  requires s0.Capacity() >= 2
  ensures s'.EXECUTING?
  ensures s'.PC() == 0x2
  ensures s'.Operands() == s0.Operands() + 2
{
  ValidJumpDest(s0);
  var s1 := Push0(s0);
  var s2 := Dup(s1, 1);
  s2
}

/** Code starting at 0x2 */
function {:opaque} ExecuteFromTag_1(s0: EvmState.ExecutingState): (s': EvmState.State)
  requires s0.PC() == 0x2 as nat
  // Net Operands effect 0
  requires s0.Operands() >= 1
  // Net Capacity effect 0
  requires s0.Capacity() >= 2
  ensures s'.EXECUTING?
  ensures s'.PC() ==  0x13 || s'.PC() == 0xa
  ensures s'.Operands() == s0.Operands() + 0
{
  ValidJumpDest(s0);
  var s1 := JumpDest(s0);
  var s2 := Push1(s1, 0x0a);
  var s3 := Dup(s2, 2);
  var s4 := Bytecode.Lt(s3);
  var s5 := Push1(s4, 0x13);
  var s6 := JumpI(s5);
  s6
}

/** Code starting at 0xa */
function {:opaque} ExecuteFromTag_2(s0: EvmState.ExecutingState): (s': EvmState.State)
  requires s0.PC() == 0xa as nat
  // Net Operands effect 0
  requires s0.Operands() >= 2
  // Net Capacity effect 0
  requires s0.Capacity() >= 0
  ensures s'.RETURNS?
{
  ValidJumpDest(s0);
  var s1 := Pop(s0);
  var s2 := Push1(s1, 0x40);
  var s3 := Bytecode.MStore(s2);
  var s4 := Push1(s3, 0x20);
  var s5 := Push1(s4, 0x40);
  var s6 := Return(s5);
  s6
}

/** Code starting at 0x13 */
function {:opaque} ExecuteFromTag_3(s0: EvmState.ExecutingState): (s': EvmState.State)
  requires s0.PC() == 0x13 as nat
  // Net Operands effect 0
  requires s0.Operands() >= 2
  // Net Capacity effect 0
  requires s0.Capacity() >= 2
  ensures s'.EXECUTING?
  ensures s'.PC() ==  0x02
  ensures s'.Operands() == s0.Operands() + 0
{
  ValidJumpDest(s0);
  var s1 := JumpDest(s0);
  var s2 := Swap(s1, 1);
  var s3 := Push1(s2, 0x01);
  var s4 := Push1(s3, 0x0a);
  var s5 := Swap(s4, 2);
  var s6 := Add(s5);
  var s7 := Swap(s6, 2);
  var s8 := Swap(s7, 1);
  var s9 := Pop(s8);
  var s10 := Push1(s9, 0x02);
  var s11 := Jump(s10);
  s11
}
}
