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


include "../utils/int.dfy"

//    StackElem already exists but uses the Int module in this project.
//    The bytecode in the Dafny EVM also uses a module name Int and if we import
//    StackElem this creates a conflict.
//    For the time being, we just re-declare locally StackElem and use
//    the Int defined in the Dafny EVM module Myint.
//    The same holds for CFGState so we also use a local EState declaration here.
module AbstractState {

  import opened Int

  datatype EState = EState(pc: nat, stack: seq<Int.u256>)
  {
    function Operands(): nat { |stack| }
  }
}

/**
  * Provides the abstract semantics for external calls.
  */
module AbstractSemantics {

  import opened AbstractState

  function Stop(s: EState): (s': EState)
  {
    EState(s.pc + 1, s.stack)
  }

  // Arithmetic op

  function Add(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Sub(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Mul(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Div(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function SDiv(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Mod(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function SMod(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function AddMod(s: EState): (s': EState)
    requires s.Operands() >= 3
  {
    EState(s.pc + 1, [0] + s.stack[3..])
  }

  function MulMod(s: EState): (s': EState)
    requires s.Operands() >= 3
  {
    EState(s.pc + 1, [0] + s.stack[3..])
  }

  function Exp(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function SignExtend(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  //  Comparison operators

  function Lt(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Gt(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function SLt(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function SGt(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Eq(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function IsZero(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  // Bitwise op

  function And(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Or(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Xor(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Not(s: EState): (s': EState)
    requires s.Operands() >= 1
    ensures s'.Operands() == s.Operands()
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function Byte(s: EState): (s': EState)
    requires s.Operands() >= 2
    ensures s'.Operands() == s.Operands() - 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Shr(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Shl(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  function Sar(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  //  Keccak256

  function Keccak256(s: EState): (s': EState)
    requires s.Operands() >= 2
    ensures s'.Operands() == s.Operands() - 1
  {
    EState(s.pc + 1, [0] + s.stack[2..])
  }

  //  Env op

  function Address(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function Balance(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function Origin(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function Caller(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function CallValue(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function CallDataLoad(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function CallDataSize(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function CallDataCopy(s: EState): (s': EState)
    requires s.Operands() >= 3
  {
    EState(s.pc + 1, s.stack[3..])
  }

  function CodeSize(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function CodeCopy(s: EState): (s': EState)
    requires s.Operands() >= 3
  {
    EState(s.pc + 1, s.stack[3..])
  }

  function GasPrice(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function ExtCodeSize(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function ExtCodeCopy(s: EState): (s': EState)
    requires s.Operands() >= 4
  {
    EState(s.pc + 1, s.stack[4..])
  }

  function ReturnDataSize(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function ReturnDataCopy(s: EState): (s': EState)
    requires s.Operands() >= 3
  {
    EState(s.pc + 1, s.stack[3..])
  }

  function ExtCodeHash(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  //  Block information

  function BlockHash(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function CoinBase(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function TimeStamp(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function Number(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function Difficulty(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function GasLimit(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function ChainID(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function SelfBalance(s: EState): (s': EState)
    ensures s'.Operands() == s.Operands() + 1
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function BaseFee(s: EState): (s': EState)
    ensures s'.Operands() == s.Operands() + 1
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  //  Stack, memory and storage op

  function Pop(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, s.stack[1..])
  }

  function MLoad(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function MStore(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, s.stack[2..])
  }

  function MStore8(s: EState): (s': EState)
    requires s.Operands() >= 2
  {
    EState(s.pc + 1, s.stack[2..])
  }

  function SLoad(s: EState): (s': EState)
    requires s.Operands() >= 1
    ensures s'.Operands() == s.Operands()
  {
    EState(s.pc + 1, [0] + s.stack[1..])
  }

  function SStore(s: EState): (s': EState)
    requires s.Operands() >= 2
    ensures s'.Operands() == s.Operands() - 2
  {
    EState(s.pc + 1, s.stack[2..])
  }

  function Jump(s: EState): (s': EState)
    requires s.Operands() >= 1
    // requires s.stack[0].Value?
  {
    EState(s.stack[0] as nat, s.stack[1..])
  }

  function JumpI(s: EState): (s': EState)
    requires s.Operands() >= 2
    ensures s'.pc == s.stack[0] as nat || s'.pc == s.pc + 1
    ensures s'.stack == s.stack[2..]
  {
    EState(if s.stack[1] > 0 then s.stack[0] as nat else s.pc + 1 as nat, s.stack[2..])
  }

  function MSize(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function Gas(s: EState): (s': EState)
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function JumpDest(s: EState): (s': EState)
  {
    EState(s.pc + 1, s.stack)
  }

  function Push0(s: EState): (s': EState)
    ensures s'.Operands() == s.Operands() + 1
    ensures s'.stack[1..] == s.stack
  {
    EState(s.pc + 1, [0] + s.stack)
  }

  function PushN(s: EState, n: nat, k: nat): (s': EState)
    requires 1 <= n <= 32
    requires k <= Int.MAX_U256
    ensures s'.Operands() == s.Operands() + 1
    ensures s'.stack[1..] == s.stack
  {
    EState(s.pc + n + 1, [k as Int.u256] + s.stack)
  }

  function Dup(s: EState, k: nat): (s': EState)
    requires s.Operands() >= k > 0
    ensures s'.stack == [s.stack[k - 1]] + s.stack
  {
    EState(s.pc + 1, [s.stack[k - 1]] + s.stack)
  }

  function Swap(s: EState, k: nat): (s': EState)
    requires 1 <= k <= 16
    requires s.Operands() > k
  {
    EState(s.pc + 1, s.stack[0 := s.stack[k]][k := s.stack[0]])
  }

  //  Log op
  function LogN(s: EState, n: nat): (s': EState)
    requires n <= 4
    requires s.Operands() >= n + 2
    ensures s'.Operands() == s.Operands() - (n + 2)
  {
    EState(s.pc + 1, s.stack[n + 2..])
  }

  //  System op

  function Create(s: EState): (s': EState)
    requires s.Operands() >= 3
  {
    EState(s.pc + 1, [0] + s.stack[3..])
  }

  function Call(s: EState): (s': EState)
    requires s.Operands() >= 7
  {
    EState(s.pc + 1, [0] + s.stack[7..])
  }

  function CallCode(s: EState): (s': EState)
    requires s.Operands() >= 7
  {
    EState(s.pc + 1, [0] + s.stack[7..])
  }

  function Return(s: EState): (s': EState)
  {
    EState(s.pc + 1, s.stack)
  }

  function DelegateCall(s: EState): (s': EState)
    requires s.Operands() >= 6
  {
    EState(s.pc + 1, [0] + s.stack[6..])
  }

  function Create2(s: EState): (s': EState)
    requires s.Operands() >= 4
  {
    EState(s.pc + 1, [0] + s.stack[4..])
  }

  function StaticCall(s: EState): (s': EState)
    requires s.Operands() >= 6
  {
    EState(s.pc + 1, [0] + s.stack[6..])
  }

  function Revert(s: EState): (s': EState)
  {
    EState(s.pc + 1, s.stack)
  }

  function SelfDestruct(s: EState): (s': EState)
    requires s.Operands() >= 1
  {
    EState(s.pc + 1, s.stack[1..])
  }

}
