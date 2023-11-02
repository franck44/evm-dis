
// Dafny program verifier finished with 1 verified, 0 errors
// include "../../../../../../evm-dafny/src/dafny/state.dfy"
// include "../../../../../../evm-dafny/src/dafny/bytecode.dfy"

module DafnyEVMProofObject {
//   import opened Int
//   import EvmState
//   import opened Bytecode
    /** Lemma for Jumpdest */
//   lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)
//     ensures s.IsJumpDest(0x7 as u256)
//     ensures s.IsJumpDest(0x10 as u256)


  /** Code starting at 0x0 */
  function {:opaque} ExecuteFromTag_0(cfg: string := ""): (cfg': string)
    // requires s0.PC() == 0x0 as nat
    // requires s0.Operands() >= 0
    // requires s0.Capacity() >= 3
    // ensures s'.RETURNS?
    // ensures s'.PC() ==  0x10
    // ensures s'.Operands() == s0.Operands() + 2
    // ensures s'.PC() ==  0x07
    // ensures s'.Operands() == s0.Operands() + 2 - 1
  {
    // ValidJumpDest(s0);
    // var s1 := Push1(s0, 0x07);
    var cfg1 := cfg + "\n" + "PUSH1 0x07";
    // var s2 := Push1(s1, 0x08);
    var cfg2 := cfg1 + "\n" + "PUSH1 0x08";
    // var s3 := Push1(s2, 0x10);
    var cfg3 := cfg2 + "\n" + "PUSH1 0x10";
    // var s4 := Jump(s3);
    var cfg4 := cfg3 + "\n" + "JUMP";
    ExecuteFromTag_2_from_0(cfg4)
  }

  /** Code starting at 0x7 */
  function {:opaque} ExecuteFromTag_1_from2(cfg: string): (cfg': string)
    // requires s0.PC() == 0x7 as nat
    // requires s0.Operands() >= 1
    // requires s0.Capacity() >= 1
    // ensures s'.RETURNS?
  {
    // ValidJumpDest(s0);
    // var s1 := JumpDest(s0);
    var cfg1 := cfg + "\n" + "JUMPDEST";
    // var s2 := Push1(s1, 0x40);
    var cfg2 := cfg1 + "\n" + "PUSH1 0x40";
    // var s3 := Bytecode.MStore(s2);
    var cfg3 := cfg2 + "\n" + "MSTORE";
    // var s4 := Push1(s3, 0x20);
    var cfg4 := cfg3 + "\n" + "PUSH 0x20";
    // var s5 := Push1(s4, 0x40);
    var cfg5 := cfg4 + "\n" + "PUSH 0x40";
    // var s6 := Return(s5);
    var cfg6 := cfg5 + "\n" + "RETURN";

    cfg6
  }

  /** Code starting at 0x10 */
  function {:opaque} ExecuteFromTag_2_from_0(cfg: string): (cfg': string)
    // requires s0.PC() == 0x10 as nat
    // requires s0.Operands() >= 2
    // requires s0.Capacity() >= 0
    // requires s0.Peek(1) == 0x07
    // requires s0.IsJumpDest(s0.Peek(1))
    // ensures s'.RETURNS?
    // ensures s'.PC() ==  s0.Peek(1) as nat
    // ensures s'.PC() ==  0x07
    // ensures s'.Operands() == s0.Operands() - 1
  {
    // ValidJumpDest(s0);
    // var s1 := JumpDest(s0);
    var cfg1 := cfg + "\n" + "JUMPDEST";
    // var s2 := Swap(s1, 1);
    var cfg2 := cfg1 + "\n" + "SWAP1";
    // var s3 := Jump(s2);
    var cfg3 := cfg2 + "\n" + "JUMP";
    ExecuteFromTag_1_from2(cfg3)
  }

  method {:main} Main() {
    var r := ExecuteFromTag_0("");
    print r, "\n";
  }

}
