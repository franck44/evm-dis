
// Dafny program verifier finished with 1 verified, 0 errors
// include "./simpleLoop.dfy"
// import opened DafnyEVMProofObject
const JUMPDESTS := [ 0x2, 0x13]


// method Test1(s0: EvmState.ExecutingState)
//   requires ExecuteFromTag_0.requires(s0)
// {
// //  assert s0.Capacity() == 1024 - s0.Operands();
//   var s' := ExecuteFromTag_0(s0);
//   assert s'.PC() == 0x10;
// }

// method Test2(s0: EvmState.ExecutingState)
//   requires ExecuteFromTag_0.requires(s0)

// {
//   var s1 := ExecuteFromTag_0(s0);
//   assert s1.PC() == 0x10;
//   ValidJumpDest(s1);

//   var s2 := ExecuteFromTag_2(s1);
//   assert s2.EXECUTING?;
//   assert s2.PC() == 0x7;

//   ValidJumpDest(s2);
//   var s3 := ExecuteFromTag_1(s2);
//   assert s3.RETURNS?;

// }

// function R1(s0: EvmState.ExecutingState): EvmState.State
//   requires ExecuteFromTag_0.requires(s0)
//   ensures R1(s0).EXECUTING?
//   ensures R1(s0).PC() == 0x10
// //   ensures R1(s0).Operands() >= 2
// //   ensures R1(s0).Peek(1) == 0x7
// {
//   ExecuteFromTag_0(s0)
// }

// function R2(s0: EvmState.ExecutingState): EvmState.State
//   requires ExecuteFromTag_0.requires(s0)
//   ensures R2(s0).EXECUTING?
//   ensures R2(s0).PC() == 0x7
// {
//   var s1 := R1(s0);
//   ValidJumpDest(s1);

//   ExecuteFromTag_2(s1)
// }

// function R3(s0: EvmState.ExecutingState): EvmState.State
//   requires ExecuteFromTag_0.requires(s0)
//   ensures R3(s0).RETURNS?
// {
//   var s1 := R2(s0);
//   ValidJumpDest(s1);

//   ExecuteFromTag_1(s1)
// }

