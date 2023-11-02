
// Dafny program verifier finished with 1 verified, 0 errors
include "../../../../../../evm-dafny/src/dafny/state.dfy"
include "../../../../../../evm-dafny/src/dafny/bytecode.dfy"

module DafnyEVMProofObject {
  import opened Int
  import EvmState
  import opened Bytecode
    /** Lemma for Jumpdest */
  lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)
    ensures s.IsJumpDest(0x7 as u256)
    ensures s.IsJumpDest(0x10 as u256)

  const JUMPDESTS := { 0x7, 0x10}

  /** Code starting at 0x0 */
  function {:notopaque} ExecuteFromTag_0(s0: EvmState.ExecutingState): (s': EvmState.State)
    requires s0.PC() == 0x0 as nat
    requires s0.Operands() == 0
    // requires s0.Capacity() >= 3
    ensures s'.EXECUTING?
    ensures s'.PC() ==  0x10
    ensures s'.Operands() == s0.Operands() + 2
    ensures s'.IsJumpDest(s'.Peek(1))
    // ensures s'.Peek(1) == 0x7
  {
    ValidJumpDest(s0);
    var s1 := Push1(s0, 0x07);
    var s2 := Push1(s1, 0x08);
    var s3 := Push1(s2, 0x10);
    var s4 := Jump(s3);
    s4
  }

  /** Code starting at 0x7 */
  function {:notopaque} ExecuteFromTag_1(s0: EvmState.ExecutingState): (s': EvmState.State)
    requires s0.PC() == 0x7 as nat
    requires s0.Operands() >= 1
    requires s0.Capacity() >= 1
    ensures s'.RETURNS?
  {
    ValidJumpDest(s0);
    var s1 := JumpDest(s0);
    var s2 := Push1(s1, 0x40);
    var s3 := Bytecode.MStore(s2);
    var s4 := Push1(s3, 0x20);
    var s5 := Push1(s4, 0x40);
    var s6 := Return(s5);
    s6
  }

  /** Code starting at 0x10 */
  function {:notopaque} ExecuteFromTag_2(s0: EvmState.ExecutingState): (s': EvmState.State)
    requires s0.PC() == 0x10 as nat
    requires s0.Operands() >= 2
    requires s0.Capacity() >= 0
    requires s0.IsJumpDest(s0.Peek(1))
    ensures s'.EXECUTING?
    ensures s'.PC() ==  s0.Peek(1) as nat
    ensures s'.Operands() == s0.Operands() - 1
  {
    ValidJumpDest(s0);
    var s1 := JumpDest(s0);
    var s2 := Swap(s1, 1);
    var s3 := Jump(s2);
    s3
  }

  function branch1(s0: EvmState.ExecutingState): (s': EvmState.State)
    requires ExecuteFromTag_0.requires(s0)
    ensures s'.EXECUTING?
    ensures s'.PC() == 0x7
  {
    var s1 := ExecuteFromTag_0(s0);
    var s2 := ExecuteFromTag_2(s1);
    s2
  }

}
