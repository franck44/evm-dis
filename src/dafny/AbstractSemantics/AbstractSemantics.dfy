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

// include "../../../../evm-dafny/src/dafny/state.dfy"
// include "../../../../evm-dafny/src/dafny/bytecode.dfy"
include "../utils/int.dfy"

//    StackElem already exists but uses the Int module in this project.
//    The bytecode in the Dafny EVM also uses a module name Int and if we import
//    StackElem this creates a conflict.
//    For the time being, we just re-declare locally StackElem and use
//    the Int defined in the Dafny EVM module int.
//    The same holds for CFGState so we also use a local EState declaration here.
module AbstractState {

  import opened Int

  //   datatype StackElem = Value(v: Int.u256) | Random(s: string := "")

  datatype EState = EState(pc: nat, stack: seq<Int.u256>)
  {
    // predicate Abstracts(st: ExecutingState)
    //   // requires IsValid()
    // {
    //   && st.PC() == pc
    //      // && |stack| <= 1024
    //      // &&
    //   && |st.GetStack().contents| == |stack|
    //   && st.Operands() == Operands()
    //      //   && forall k:: 0 <= k < Operands() && Peek(k).Value? ==> st.Peek(k) == Extract(k)
    //   && forall k:: 0 <= k < Operands() && stack[k].Value? ==> st.Peek(k) == stack[k].v
    // }

    predicate IsValid() {
      //   && Operands() <= 1024
      && |stack| <= 1024
      //   && Operands() + Capacity() == 1024
    }

    function Operands(): nat
      //   requires IsValid()
    {
      |stack|
    }

    function Capacity(): nat
      requires IsValid()
    {
      1024 - |stack|
    }

    // function Peek(k: nat): StackElem
    //   requires IsValid()
    //   requires k < Operands()
    // {
    //   stack[k]
    // }

    // function Extract(k: nat): Int.u256
    //   requires IsValid()
    //   requires k < Operands()
    //   requires Peek(k).Value?
    // {
    //   stack[k].v
    // }
  }
}

/**
  * Provides the abstract semantics for external calls.
  */
module AbstractSemantics {

  //   import opened EvmState
  //   import Bytecode
  import opened AbstractState

  //   function Call(st: EvmState.ExecutingState): (st': EvmState.ExecutingState)
  //     // ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
  //     requires st.Operands() >= 7 // && (st.WritesPermitted() || st.Peek(2) == 0)
  //     // ensures st' == ERROR(STACK_UNDERFLOW)  <==> st.Operands() < 7
  //     // ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==>
  //     // st.Operands() >= 7 && !st.WritesPermitted() && st.Peek(2) > 0
  //     ensures st'.EXECUTING?
  //     ensures st'.Operands() == st.Operands() - 7 + 1
  //     ensures st'.Capacity() == st.Capacity() + 7 - 1
  //     ensures st'.GetStack().contents[1..] == st.GetStack().contents[7..]
  //     // ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 6)

  //     // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(7, st.Operands())
  //     ensures st'.PC() == st.PC() + 1
  //     ensures st'.WritesPermitted() == st.WritesPermitted()

  function Call(s: EState): (s': EState)
    // requires s.IsValid()
    // ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    requires s.Operands() >= 7 // && (st.WritesPermitted() || st.Peek(2) == 0)
    // ensures st' == ERROR(STACK_UNDERFLOW)  <==> st.Operands() < 7
    // ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==>
    // st.Operands() >= 7 && !st.WritesPermitted() && st.Peek(2) > 0
    // ensures s'.IsValid()
    // ensures st'.Operands() == st.Operands() - 7 + 1
    // ensures st'.Capacity() == st.Capacity() + 7 - 1
    // ensures st'.GetStack().contents[1..] == st.GetStack().contents[7..]
    // ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 6)

    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(7, st.Operands())
    // ensures st'.PC() == st.PC() + 1
    // ensures st'.WritesPermitted() == st.WritesPermitted()
  {
    EState(s.pc + 1, [0] + s.stack[7..])
  }

  function StaticCall(s: EState): (s': EState)
    // requires s.IsValid()
    // ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    requires s.Operands() >= 6 // && (st.WritesPermitted() || st.Peek(2) == 0)
    // ensures st' == ERROR(STACK_UNDERFLOW)  <==> st.Operands() < 7
    // ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==>
    // st.Operands() >= 7 && !st.WritesPermitted() && st.Peek(2) > 0
    // ensures s'.IsValid()
    // ensures st'.Operands() == st.Operands() - 7 + 1
    // ensures st'.Capacity() == st.Capacity() + 7 - 1
    // ensures st'.GetStack().contents[1..] == st.GetStack().contents[7..]
    // ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 6)

    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(7, st.Operands())
    // ensures st'.PC() == st.PC() + 1
    // ensures st'.WritesPermitted() == st.WritesPermitted()
  {
    EState(s.pc + 1, [0] + s.stack[6..])
  }


  //   lemma SimulationCorrectness(s: EState, n: nat, k: nat, st: ExecutingState)
  //     ensures Pop.requires(s) &&  s.Abstracts(st) ==> Pop(s).Abstracts(Bytecode.Pop(st))
  //     ensures Dup.requires(s, k) &&  s.Abstracts(st) ==> Dup(s, k).Abstracts(Bytecode.Dup(st, k))
  //     ensures Swap.requires(s, k) &&  s.Abstracts(st) ==> Swap(s, k).Abstracts(Bytecode.Swap(st, k))
  //     ensures MLoad.requires(s) &&  s.Abstracts(st) ==> MLoad(s).Abstracts(Bytecode.MLoad(st))
  //     ensures MStore.requires(s) &&  s.Abstracts(st) ==> MStore(s).Abstracts(Bytecode.MStore(st))
  //     ensures Pop.requires(s) &&  s.Abstracts(st) ==> Pop(s).Abstracts(Bytecode.Pop(st))
  //   {   //  Thanks Dafny
  //   }

  //   lemma SimulationCorrectnessStackOp(s: EState, n: nat, k: nat, st: ExecutingState)
  //     requires s.Abstracts(st)
  //     ensures Bytecode.Pop(st).EXECUTING? ==> Pop.requires(s) && Pop(s).Abstracts(Bytecode.Pop(st))
  //     ensures k > 0 && Bytecode.Dup(st, k).EXECUTING? ==> Dup.requires(s, k) && Dup(s, k).Abstracts(Bytecode.Dup(st, k))
  //     ensures 1 <= k <= 16 && Bytecode.Swap(st, k).EXECUTING? ==> Swap.requires(s, k) && Swap(s, k).Abstracts(Bytecode.Swap(st, k))
  //   {   //  Thanks Dafny
  //   }

  //   lemma SimulationCorrectnessV2MemOp(s: EState, n: nat, k: nat, st: ExecutingState)
  //     requires s.Abstracts(st)
  //     ensures Bytecode.MLoad(st).EXECUTING? ==> MLoad.requires(s) && MLoad(s).Abstracts(Bytecode.MLoad(st))
  //     ensures Bytecode.MStore(st).EXECUTING? ==> MStore(s).Abstracts(Bytecode.MStore(st))
  //   {   //  Thanks Dafny
  //   }

  function PushN(s: EState, n: nat, k: nat): (s': EState)
    // requires s.IsValid()
    requires 1 <= n <= 32
    requires k <= Int.MAX_U256
    // requires s.Capacity() >= 1

    ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    ensures s'.stack[1..] == s.stack
    // ensures s'.IsValid()
  {
    EState(s.pc + n + 1, [k as Int.u256] + s.stack)
  }

  function Push0(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1

    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    ensures s'.stack[1..] == s.stack
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function Pop(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1

    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, s.stack[1..])
  }

  function Dup(s: EState, k: nat): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= k > 0
    // requires s.Capacity() >= 1

    // ensures s'.IsValid()
    ensures s'.stack == [s.stack[k - 1]] + s.stack
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [s.stack[k - 1]] + s.stack)
  }

  function Swap(s: EState, k: nat): (s': EState)
    // requires s.IsValid()
    requires 1 <= k <= 16
    requires s.Operands() > k

    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity()
  {
    EState(s.pc + 1, s.stack[0 := s.stack[k]][k := s.stack[0]])
  }

  function SLoad(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1

    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity()
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function SStore(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2

    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() - 2
    // ensures s'.Capacity() == s.Capacity()
  {
    EState(s.pc + 1, s.stack[2..])
  }

  function MLoad(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1

    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity()
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function MStore(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2

    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 2
    // ensures s'.Capacity() == s.Capacity() + 2
  {
    EState(s.pc + 1, s.stack[2..])
  }

  function MStore8(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2

    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 2
    // ensures s'.Capacity() == s.Capacity() + 2
  {
    EState(s.pc + 1, s.stack[2..])
  }

  function Jump(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // requires s.stack[0].Value?
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.stack[0] as nat, s.stack[1..])
  }

  function JumpI(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // requires s.stack[0].Value?
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
    ensures s'.pc == s.stack[0] as nat || s'.pc == s.pc + 1
    ensures s'.stack == s.stack[2..]
  {

    EState(if s.stack[1] > 0 then s.stack[0] as nat else s.pc + 1 as nat, s.stack[2..])
  }

  function Add(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Sub(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Mul(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Div(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Mod(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Exp(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Byte(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Lt(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Gt(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Slt(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

   function Sgt(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Eq(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Shr(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Shl(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }


  function IsZero(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function And(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Or(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }


  function Xor(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }


  function Not(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function Address(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Operands() >= 2
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [0] + s.stack)
  }

   function Balance(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() 
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

   function SelfBalance(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Operands() >= 1
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function Gas(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Operands() >= 2
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function Keccak256(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function CallValue(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity()
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function CallDataLoad(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity()
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function CallDataCopy(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 3
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 3
    // ensures s'.Capacity() == s.Capacity() + 3
  {
    EState(s.pc + 1, s.stack[3..])
  }

  function CodeCopy(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 3
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() - 3
    // ensures s'.Capacity() == s.Capacity() + 3
  {
    EState(s.pc + 1, s.stack[3..])
  }

  function CallDataSize(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 3
    // ensures s'.Capacity() == s.Capacity() + 3
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function ExtCodeSize(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity() + 3
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }
  function Caller(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    ensures s'.stack == [0] + s.stack
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function ReturnDataSize(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() + 3
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function ReturnDataCopy(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 3
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() - 3
    // ensures s'.Capacity() == s.Capacity() + 3
  {
    EState(s.pc + 1, s.stack[3..])
  }

  function JumpDest(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    // ensures s'.stack == [0] + s.stack
  {
    EState(s.pc + 1, s.stack)
  }

  function Revert(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    // ensures s'.stack == [0] + s.stack
  {
    EState(s.pc + 1, s.stack)
  }

  function Return(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    // ensures s'.stack == [0] + s.stack
  {
    EState(s.pc + 1, s.stack)
  }

  function Stop(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    // ensures s'.stack == [0] + s.stack
  {
    EState(s.pc + 1, s.stack)
  }


  function LogN(s: EState, n: nat): (s': EState)
    requires n <= 4
    // requires s.IsValid()
    requires s.Operands() >= n + 2
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() - (n + 2)
    // ensures s'.Capacity() == s.Capacity() - 1
    // ensures s'.stack == [0] + s.stack
  {
    EState(s.pc + 1, s.stack[n + 2..])
  }


}
