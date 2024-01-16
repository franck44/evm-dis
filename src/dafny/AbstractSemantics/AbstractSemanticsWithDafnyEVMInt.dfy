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

include "../../../../evm-dafny/src/dafny/state.dfy"
include "../../../../evm-dafny/src/dafny/util/int.dfy"

/**
 *  This project and the Dafny-EVM both use an Int module.
 *  There is a name clash when we want to mix them together.
 *  For the time being the module in these files are copies
 *  of the absttact semantics but using the Dafny-EVM int instead of
 *  of this project's Int module. 
 *  The two moduels are the same so it is not an issue.
 */
module AbstractStateDafnyEVM {

  import opened Int
  import opened EvmState


  datatype StackElem = Value(v: Int.u256) | Random() 

  datatype EState = EState(pc: nat, stack: seq<StackElem>)
  {
    function Operands(): nat { |stack| }

    predicate Abstracts(st: ExecutingState) {
      && st.PC() == pc 
      && st.Operands() == Operands()
      && forall k:: 0 <= k < Operands() && stack[k].Value? ==> stack[k].v == st.GetStack().contents[k]
    }
  }
}

/**
  * Provides the abstract semantics for external calls.
  */
module AbstractSemanticsDafnyEVM {

  import opened AbstractStateDafnyEVM

  function Call(s: EState): (s': EState)
    requires s.Operands() >= 7 // && (st.WritesPermitted() || st.Peek(2) == 0)
  {
    EState(s.pc + 1, [Random()] + s.stack[7..])
  }

  function StaticCall(s: EState): (s': EState)
    requires s.Operands() >= 6 
  {
    EState(s.pc + 1, [Random()] + s.stack[6..])
  }

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
    EState(s.pc + n + 1, [Value(k as Int.u256)] + s.stack)
  }

  function Push0(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1

    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    ensures s'.stack[1..] == s.stack
  {
    EState(s.pc + 1, [Random()] + s.stack)
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
    EState(s.pc + 1, [Random()] + s.stack[1..])
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
    EState(s.pc + 1, [Random()] + s.stack[1..])
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
    requires s.stack[0].Value?
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.stack[0].v as nat, s.stack[1..])
  }

  function JumpI(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    requires s.stack[0].Value?
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
    ensures s'.pc == s.stack[0].v as nat || s'.pc == s.pc + 1
    ensures s'.stack == s.stack[2..]
//   {

//     EState(if s.stack[1] > 0 then s.stack[0] as nat else s.pc + 1 as nat, s.stack[2..])
//   }

  function Add(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Sub(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Mul(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Div(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Mod(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Exp(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Byte(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Lt(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Gt(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Slt(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

   function Sgt(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Eq(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Shr(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Shl(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }


  function IsZero(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[1..])
  }

  function And(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function Or(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }


  function Xor(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }


  function Not(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity() + 1
  {
    EState(s.pc + 1, [Random()] + s.stack[1..])
  }

  function Address(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Operands() >= 2
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [Random()] + s.stack)
  }

   function Balance(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() 
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [Random()] + s.stack[1..])
  }

   function SelfBalance(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Operands() >= 1
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [Random()] + s.stack)
  }

  function Gas(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Operands() >= 2
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [Random()] + s.stack)
  }

  function Keccak256(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 2
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() - 1
    // ensures s'.Capacity() == s.Capacity() - 1
  {
    EState(s.pc + 1, [Random()] + s.stack[2..])
  }

  function CallValue(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity()
  {
    EState(s.pc + 1, [Random()] + s.stack)
  }

  function CallDataLoad(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity()
  {
    EState(s.pc + 1, [Random()] + s.stack[1..])
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
    EState(s.pc + 1, [Random()] + s.stack)
  }

  function ExtCodeSize(s: EState): (s': EState)
    // requires s.IsValid()
    requires s.Operands() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands()
    // ensures s'.Capacity() == s.Capacity() + 3
  {
    EState(s.pc + 1, [Random()] + s.stack[1..])
  }
  function Caller(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    ensures s'.stack == [Random()] + s.stack
  {
    EState(s.pc + 1, [Random()] + s.stack)
  }

  function ReturnDataSize(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() + 3
  {
    EState(s.pc + 1, [Random()] + s.stack)
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
    // ensures s'.stack == [Random()] + s.stack
  {
    EState(s.pc + 1, s.stack)
  }

  function Revert(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    // ensures s'.stack == [Random()] + s.stack
  {
    EState(s.pc + 1, s.stack)
  }

  function Return(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    // ensures s'.stack == [Random()] + s.stack
  {
    EState(s.pc + 1, s.stack)
  }

  function Stop(s: EState): (s': EState)
    // requires s.IsValid()
    // requires s.Capacity() >= 1
    // ensures s'.IsValid()
    // ensures s'.Operands() == s.Operands() + 1
    // ensures s'.Capacity() == s.Capacity() - 1
    // ensures s'.stack == [Random()] + s.stack
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
    // ensures s'.stack == [Random()] + s.stack
  {
    EState(s.pc + 1, s.stack[n + 2..])
  }


}
