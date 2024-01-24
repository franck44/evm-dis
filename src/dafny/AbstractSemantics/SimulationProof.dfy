/*
 * Copyright 2024 Franck Cassez
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

include "./AbstractSemanticsWithDafnyEVMInt.dfy"
include "../../../../evm-dafny/src/dafny/state.dfy"
include "../../../../evm-dafny/src/dafny/bytecode.dfy"

/**
  * Provides the proof of simulation for the abstract semantics.
  *
  * The proof establishes the following for each EVM operator f.
  *     given st an EVM Executing state (non error)
  *     forall s, abstract state, such that s Abstracts st,
  *     if f can be applied to st, and f(st) is an executing state, 
  *     then f can be applied to s and the result f(s) abstracts f(st).
  * @todo this is not true for some operators as we end up in a RETURN state, so we have 
  *     to add this at some point.
  */
module SimluationProof {

  import opened EvmState
  import Bytecode
  import opened AbstractSemanticsDafnyEVM
  import opened AbstractStateDafnyEVM

  //  Arith Op
  lemma SimulationCorrectnessArithOp(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Stop(st).RETURNS? ==> Stop.requires(s) 
    ensures Bytecode.Add(st).EXECUTING? ==> Add.requires(s) && Add(s).Abstracts(Bytecode.Add(st))
    ensures Bytecode.Sub(st).EXECUTING? ==> Sub.requires(s) && Sub(s).Abstracts(Bytecode.Sub(st))
    ensures Bytecode.Mul(st).EXECUTING? ==> Mul.requires(s) && Mul(s).Abstracts(Bytecode.Mul(st))
    ensures Bytecode.Div(st).EXECUTING? ==> Div.requires(s) && Div(s).Abstracts(Bytecode.Div(st))
    ensures Bytecode.SDiv(st).EXECUTING? ==> SDiv.requires(s) && SDiv(s).Abstracts(Bytecode.SDiv(st))
    ensures Bytecode.Mod(st).EXECUTING? ==> Mod.requires(s) && Mod(s).Abstracts(Bytecode.Mod(st))
    ensures Bytecode.SMod(st).EXECUTING? ==> SMod.requires(s) && SMod(s).Abstracts(Bytecode.SMod(st))
    ensures Bytecode.AddMod(st).EXECUTING? ==> AddMod.requires(s) && AddMod(s).Abstracts(Bytecode.AddMod(st))
    ensures Bytecode.MulMod(st).EXECUTING? ==> MulMod.requires(s) && MulMod(s).Abstracts(Bytecode.MulMod(st))
    ensures Bytecode.Exp(st).EXECUTING? ==> Exp.requires(s) && Exp(s).Abstracts(Bytecode.Exp(st))
    ensures Bytecode.SignExtend(st).EXECUTING? ==> SignExtend.requires(s) && SignExtend(s).Abstracts(Bytecode.SignExtend(st))
  {   //  Thanks Dafny
  }

  //  Comp op
  lemma SimulationCorrectnessCompOp(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Lt(st).EXECUTING? ==> Lt.requires(s) && Lt(s).Abstracts(Bytecode.Lt(st))
    ensures Bytecode.Gt(st).EXECUTING? ==> Gt.requires(s) && Gt(s).Abstracts(Bytecode.Gt(st))
    ensures Bytecode.SLt(st).EXECUTING? ==> SLt.requires(s) && SLt(s).Abstracts(Bytecode.SLt(st))
    ensures Bytecode.SGt(st).EXECUTING? ==> SGt.requires(s) && SGt(s).Abstracts(Bytecode.SGt(st))
    ensures Bytecode.Eq(st).EXECUTING? ==> Eq.requires(s) && Eq(s).Abstracts(Bytecode.Eq(st))
    ensures Bytecode.IsZero(st).EXECUTING? ==> IsZero.requires(s) && IsZero(s).Abstracts(Bytecode.IsZero(st))
  {   //  Thanks Dafny
  }


  //  Bitwise Op
  lemma SimulationCorrectnessBitwiseOpSet1(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.And(st).EXECUTING? ==> And.requires(s) && And(s).Abstracts(Bytecode.And(st))
    ensures Bytecode.Or(st).EXECUTING? ==> Or.requires(s) && Or(s).Abstracts(Bytecode.Or(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessBitwiseOpSet2(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Xor(st).EXECUTING? ==> Xor.requires(s) && Xor(s).Abstracts(Bytecode.Xor(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessBitwiseOpSet3(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Not(st).EXECUTING? ==> Not.requires(s) && Not(s).Abstracts(Bytecode.Not(st))
    ensures Bytecode.Byte(st).EXECUTING? ==> Byte.requires(s) && Byte(s).Abstracts(Bytecode.Byte(st))
    ensures Bytecode.Shr(st).EXECUTING? ==> Shr.requires(s) && Shr(s).Abstracts(Bytecode.Shr(st))
    ensures Bytecode.Shl(st).EXECUTING? ==> Shl.requires(s) && Shl(s).Abstracts(Bytecode.Shl(st))
    ensures Bytecode.Sar(st).EXECUTING? ==> Sar.requires(s) && Sar(s).Abstracts(Bytecode.Sar(st))
  {   //  Thanks Dafny
  }

  //  Keccak
  lemma SimulationCorrectnessKeccak256(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Keccak256(st).EXECUTING? ==> Keccak256.requires(s) && Keccak256(s).Abstracts(Bytecode.Keccak256(st))
  {   //  Thanks Dafny
  }

  //  Env Op
  lemma SimulationCorrectnessEnvOp(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Address(st).EXECUTING? ==> Address.requires(s) && Address(s).Abstracts(Bytecode.Address(st))
    ensures Bytecode.Balance(st).EXECUTING? ==> Balance.requires(s) && Balance(s).Abstracts(Bytecode.Balance(st))
    ensures Bytecode.Origin(st).EXECUTING? ==> Origin.requires(s) && Origin(s).Abstracts(Bytecode.Origin(st))
    ensures Bytecode.Caller(st).EXECUTING? ==> Caller.requires(s) && Caller(s).Abstracts(Bytecode.Caller(st))
    ensures Bytecode.CallValue(st).EXECUTING? ==> CallValue.requires(s) && CallValue(s).Abstracts(Bytecode.CallValue(st))
    ensures Bytecode.CallDataLoad(st).EXECUTING? ==> CallDataLoad.requires(s) && CallDataLoad(s).Abstracts(Bytecode.CallDataLoad(st))
    ensures Bytecode.CallDataSize(st).EXECUTING? ==> CallDataSize.requires(s) && CallDataSize(s).Abstracts(Bytecode.CallDataSize(st))
    ensures Bytecode.CallDataCopy(st).EXECUTING? ==> CallDataCopy.requires(s) && CallDataCopy(s).Abstracts(Bytecode.CallDataCopy(st))
    ensures Bytecode.CodeSize(st).EXECUTING? ==> CodeSize.requires(s) && CodeSize(s).Abstracts(Bytecode.CodeSize(st))
    ensures Bytecode.CodeCopy(st).EXECUTING? ==> CodeCopy.requires(s) && CodeCopy(s).Abstracts(Bytecode.CodeCopy(st))
    ensures Bytecode.GasPrice(st).EXECUTING? ==> GasPrice.requires(s) && GasPrice(s).Abstracts(Bytecode.GasPrice(st))
    ensures Bytecode.ExtCodeSize(st).EXECUTING? ==> ExtCodeSize.requires(s) && ExtCodeSize(s).Abstracts(Bytecode.ExtCodeSize(st))
    ensures Bytecode.ExtCodeCopy(st).EXECUTING? ==> ExtCodeCopy.requires(s) && ExtCodeCopy(s).Abstracts(Bytecode.ExtCodeCopy(st))
    ensures Bytecode.ReturnDataSize(st).EXECUTING? ==> ReturnDataSize.requires(s) && ReturnDataSize(s).Abstracts(Bytecode.ReturnDataSize(st))
    ensures Bytecode.ReturnDataCopy(st).EXECUTING? ==> ReturnDataCopy.requires(s) && ReturnDataCopy(s).Abstracts(Bytecode.ReturnDataCopy(st))
    ensures Bytecode.ExtCodeHash(st).EXECUTING? ==> ExtCodeHash.requires(s) && ExtCodeHash(s).Abstracts(Bytecode.ExtCodeHash(st))
  { //  Thanks Dafny
  }

  //    Block Op

  lemma SimulationCorrectnessBlockOp(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.BlockHash(st).EXECUTING? ==> BlockHash.requires(s) && BlockHash(s).Abstracts(Bytecode.BlockHash(st))
    ensures Bytecode.CoinBase(st).EXECUTING? ==> CoinBase.requires(s) && CoinBase(s).Abstracts(Bytecode.CoinBase(st))
    ensures Bytecode.TimeStamp(st).EXECUTING? ==> TimeStamp.requires(s) && TimeStamp(s).Abstracts(Bytecode.TimeStamp(st))
    ensures Bytecode.Number(st).EXECUTING? ==> Number.requires(s) && Number(s).Abstracts(Bytecode.Number(st))
    ensures Bytecode.Difficulty(st).EXECUTING? ==> Difficulty.requires(s) && Difficulty(s).Abstracts(Bytecode.Difficulty(st))
    ensures Bytecode.GasLimit(st).EXECUTING? ==> GasLimit.requires(s) && GasLimit(s).Abstracts(Bytecode.GasLimit(st))
    ensures Bytecode.ChainID(st).EXECUTING? ==> ChainID.requires(s) && ChainID(s).Abstracts(Bytecode.ChainID(st))
    ensures Bytecode.SelfBalance(st).EXECUTING? ==> SelfBalance.requires(s) && SelfBalance(s).Abstracts(Bytecode.SelfBalance(st))
    ensures Bytecode.BaseFee(st).EXECUTING? ==> BaseFee.requires(s) && BaseFee(s).Abstracts(Bytecode.BaseFee(st))
  {   //  Thanks Dafny
  }

  //    Stack, memory, storage

  lemma SimulationCorrectnessPopOp(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Pop(st).EXECUTING? ==> Pop.requires(s) && Pop(s).Abstracts(Bytecode.Pop(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessMemOp(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.MLoad(st).EXECUTING? ==> MLoad.requires(s) && MLoad(s).Abstracts(Bytecode.MLoad(st))
    ensures Bytecode.MStore(st).EXECUTING? ==> MStore.requires(s) && MStore(s).Abstracts(Bytecode.MStore(st))
    ensures Bytecode.MStore8(st).EXECUTING? ==> MStore8.requires(s) && MStore8(s).Abstracts(Bytecode.MStore8(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessStoreOp(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.SLoad(st).EXECUTING? ==> SLoad.requires(s) && SLoad(s).Abstracts(Bytecode.SLoad(st))
    ensures Bytecode.SStore(st).EXECUTING? ==> SStore.requires(s) && SStore(s).Abstracts(Bytecode.SStore(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessJumps(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Jump(st).EXECUTING? && s.stack[0].Value? ==> Jump.requires(s) && Jump(s).Abstracts(Bytecode.Jump(st))
  {   //  Thanks Dafny
  }

  /**
    *    The JUMPI lemma is the most interesting one. It is the only one that requires
    *    a case split. Indeed, JUMPI can lead to two different states depending on the
    *    value of the second-topmost element  of the stack.
    */
  lemma SimulationCorrectnessJumpI(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.JumpI(st).EXECUTING? && s.stack[0].Value?  ==>
              JumpI.requires(s) && (exists s': EState :: s' == JumpI(s) && s'.Abstracts(Bytecode.JumpI(st)))
  {
    var st' := Bytecode.JumpI(st);
    if st'.EXECUTING? && s.stack[0].Value? {
      assert JumpI.requires(s);
      if st.Peek(1) > 0 {
        assert st.IsJumpDest(st.Peek(0)) ;
        assert st'.PC() == st.Peek(0) as nat;
        var s' := s.(pc := s.stack[0].v as nat, stack := s.stack[2..]);
        //  Here we are resolving non-determinism in JumpI
        assume s' == JumpI(s);
        assert s'.Abstracts(Bytecode.JumpI(st));
      } else {
        assert st'.PC() == st.PC() + 1;
        var s' := s.(pc := s.pc + 1, stack := s.stack[2..]);
        //  Here we are resolving non-determinism in JumpI
        assume s' == JumpI(s);
        assert s'.Abstracts(Bytecode.JumpI(st));
      }
    }
  }

  lemma SimulationCorrectnessMSize(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.MSize(st).EXECUTING? ==> MSize.requires(s) && MSize(s).Abstracts(Bytecode.MSize(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessGas(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Gas(st).EXECUTING? ==> Gas.requires(s) && Gas(s).Abstracts(Bytecode.Gas(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessJumpDest(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.JumpDest(st).EXECUTING? ==> JumpDest.requires(s) && JumpDest(s).Abstracts(Bytecode.JumpDest(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessPush0Op(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.Push0(st).EXECUTING? ==> Push0.requires(s) && Push0(s).Abstracts(Bytecode.Push0(st))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessPushNOp(s: EState, n: nat, k: nat, v: Int.u256, st: ExecutingState)
    requires s.Abstracts(st)
    ensures 1 <= n <= 32 && v as nat <= Int.MaxUnsignedN(n) && Bytecode.PushN(st, n, v).EXECUTING? ==> PushN.requires(s, n, v as nat) && PushN(s, n, v as nat).Abstracts(Bytecode.PushN(st, n, v))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessDupNOp(s: EState, n: nat, k: nat, v: Int.u256, st: ExecutingState)
    requires s.Abstracts(st)
    ensures k > 0 && Bytecode.Dup(st, k).EXECUTING? ==> Dup.requires(s, k) && Dup(s, k).Abstracts(Bytecode.Dup(st, k))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessSwapNOp(s: EState, n: nat, k: nat, v: Int.u256, st: ExecutingState)
    requires s.Abstracts(st)
    ensures 1 <= k <= 16 && Bytecode.Swap(st, k).EXECUTING? ==> Swap.requires(s, k) && Swap(s, k).Abstracts(Bytecode.Swap(st, k))
  {   //  Thanks Dafny
  }

  //    LogN op
  lemma SimulationCorrectnessLogNOp(s: EState, n: nat, st: ExecutingState)
    requires s.Abstracts(st)
    ensures 0 < n <= 4 && Bytecode.LogN(st, n).EXECUTING? ==> LogN.requires(s, n) && LogN(s, n).Abstracts(Bytecode.LogN(st, n))
  {   //  Thanks Dafny
  }

  //  System op
  //    The system op return CONTINUING so we don't verify them (*for now*) against the Dafny-EVm semantics.
  lemma SimulCorrectnessSystemOp(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    // ensures Bytecode.Create(st).EXECUTING? ==> AbstractSemanticsDafnyEVM.Create.requires(s) && AbstractSemanticsDafnyEVM.Create(s).Abstracts(Bytecode.Create(st))
    // ensures Bytecode.Call(st).EXECUTING? ==> AbstractSemanticsDafnyEVM.Call.requires(s) && AbstractSemanticsDafnyEVM.Call(s).Abstracts(Bytecode.Call(st))
    // ensures Bytecode.CallCode(st).EXECUTING? ==> AbstractSemanticsDafnyEVM.CallCode.requires(s) && AbstractSemanticsDafnyEVM.CallCode(s).Abstracts(Bytecode.CallCode(st))
    ensures Bytecode.Return(st).RETURNS? ==> AbstractSemanticsDafnyEVM.Return.requires(s) 
  {   //  Thanks Dafny
  }

  lemma SimulCorrectnessSystemOpSet2(s: EState, st: ExecutingState)
    requires s.Abstracts(st)
    // ensures Bytecode.DelegateCall(st).EXECUTING? ==> AbstractSemanticsDafnyEVM.DelegateCall.requires(s) && AbstractSemanticsDafnyEVM.DelegateCall(s).Abstracts(Bytecode.DelegateCall(st))
    // ensures Bytecode.Create2(st).EXECUTING? ==> Create2.requires(s) && Create2(s).Abstracts(Bytecode.Create2(st))
    // ensures Bytecode.StaticCall(st).EXECUTING? ==> AbstractSemanticsDafnyEVM.StaticCall.requires(s) && AbstractSemanticsDafnyEVM.StaticCall(s).Abstracts(Bytecode.StaticCall(st))
    ensures Bytecode.Revert(st).EXECUTING? ==> Revert.requires(s)
    // ensures Bytecode.SelfDestruct(st).EXECUTING? ==> SelfDestruct.requires(s) && SelfDestruct(s).Abstracts(Bytecode.SelfDestruct(st)) 
  {   //  Thanks Dafny
  }

}
