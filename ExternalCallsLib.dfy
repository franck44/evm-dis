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

include "../evm-dafny/src/dafny/state.dfy"
include "../evm-dafny/src/dafny/bytecode.dfy"

/**
  * Provides the abstract semantics for external calls.
  */
module ExternalCallLib {

  import opened EvmState
  import Bytecode

  function Call(st: EvmState.ExecutingState): (st': EvmState.ExecutingState)
    // ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    requires st.Operands() >= 7 // && (st.WritesPermitted() || st.Peek(2) == 0)
    // ensures st' == ERROR(STACK_UNDERFLOW)  <==> st.Operands() < 7
    // ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==>
    // st.Operands() >= 7 && !st.WritesPermitted() && st.Peek(2) > 0
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() - 7 + 1
    ensures st'.Capacity() == st.Capacity() + 7 - 1
    ensures st'.GetStack().contents[1..] == st.GetStack().contents[7..]
    // ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 6)

    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(7, st.Operands())
    ensures st'.PC() == st.PC() + 1
    ensures st'.WritesPermitted() == st.WritesPermitted()
}

/**
  * Provides the abstract semantics for 
  * EVM bytecode instructions.
  */
module StackSemantics {

  import opened EvmState
  import Bytecode

  function Call(st: EvmState.ExecutingState): (st': EvmState.ExecutingState)
    // ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    requires st.Operands() >= 7 // && (st.WritesPermitted() || st.Peek(2) == 0)
    // ensures st' == ERROR(STACK_UNDERFLOW)  <==> st.Operands() < 7
    // ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==>
    // st.Operands() >= 7 && !st.WritesPermitted() && st.Peek(2) > 0
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() - 7 + 1
    ensures st'.Capacity() == st.Capacity() + 7 - 1
    ensures st'.GetStack().contents[1..] == st.GetStack().contents[7..]
    // ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 6)

    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(7, st.Operands())
    ensures st'.PC() == st.PC() + 1
    ensures st'.WritesPermitted() == st.WritesPermitted()

  function {:opaque} PushN(st: EvmState.ExecutingState, n: nat, k: nat): (st': EvmState.ExecutingState)
    requires 1 <= n <= 32
    requires k <= Int.MAX_U256
    // Ensure k is within bounds
    // requires (k as nat) <= Int.MaxUnsignedN(n)
    requires st.Capacity() >= 1
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() + 1
    ensures st'.Capacity() == st.Capacity() - 1
    ensures forall k:: 0 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k + 1)
    ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k - 1)
    ensures st'.Peek(0) == k as Int.u256

    ensures st'.GetStack().contents == [k as Int.u256] + st.GetStack().contents
    ensures st'.WritesPermitted() == st.WritesPermitted()
    ensures st'.PC() == st.PC() + n + 1
  {
    assume (k as nat) <= Int.MaxUnsignedN(n);
    Bytecode.PushN(st, n, k as Int.u256)
  }

  function {:opaque} Dup(st: ExecutingState, k: nat): (st': ExecutingState)
    requires k > 0
    requires st.Capacity() >= 1 && st.Operands() >= k
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() + 1
    ensures st'.Capacity() == st.Capacity() - 1
    ensures forall k:: 0 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k + 1)
    ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k - 1)
    ensures st'.Peek(0) == st.Peek(k - 1)

    ensures st'.GetStack().contents == [st.GetStack().contents[k - 1]] + st.GetStack().contents
    ensures st'.WritesPermitted() == st.WritesPermitted()
    ensures st'.PC() == st.PC() + 1
  {
    Bytecode.Dup(st, k)
  }

  function {:opaque} MLoad(st: ExecutingState): (st': ExecutingState)
    requires st.Operands() >= 1
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands()
    ensures st'.Capacity() == st.Capacity()
    ensures forall k:: 1 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k)
    // ensures forall k:: 0 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 2)

    ensures st'.GetStack().contents[1..] == st.GetStack().contents[1..]
    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(1, st.Operands())
    ensures st'.WritesPermitted() == st.WritesPermitted()
    ensures st'.PC() == st.PC() + 1
  {
    Bytecode.MLoad(st)
  }

  function {:opaque} MStore(st: ExecutingState): (st': ExecutingState)
    requires st.Operands() >= 2
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() - 2
    ensures st'.Capacity() == st.Capacity() + 2

    ensures forall k:: 2 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k - 2)
    ensures forall k:: 0 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 2)

    ensures st'.GetStack().contents == st.GetStack().contents[2..]
    // ensures st'.GetStack() == st.SlicePeek(2, st.Operands())
    ensures st'.WritesPermitted() == st.WritesPermitted()
    ensures st'.PC() == st.PC() + 1
  {
    Bytecode.MStore(st)
  }

  function {:opaque} Sub(st: ExecutingState): (st': ExecutingState)
    requires st.Operands() >= 2
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() - 1
    ensures st'.Capacity() == st.Capacity() + 1

    ensures st'.GetStack().contents[1..] == st.GetStack().contents[2..]
    ensures forall k:: 2 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k - 1)
    ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 1)

    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(2, st.Operands())
    ensures st'.WritesPermitted() == st.WritesPermitted()
    ensures st'.PC() == st.PC() + 1
  {
    Bytecode.Sub(st)
  }

  function {:opaque} Mul(st: ExecutingState): (st': ExecutingState)
    requires st.Operands() >= 2
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() - 1
    ensures st'.Capacity() == st.Capacity() + 1
    ensures st'.GetStack().contents[1..] == st.GetStack().contents[2..]
    ensures forall k:: 2 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k - 1)
    ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 1)


    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(2, st.Operands())
    ensures st'.WritesPermitted() == st.WritesPermitted()
    ensures st'.PC() == st.PC() + 1
  {
    Bytecode.Mul(st)
  }

  function {:opaque} Exp(st: ExecutingState): (st': ExecutingState)
    requires st.Operands() >= 2
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() - 1
    ensures st'.Capacity() == st.Capacity() + 1

    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(2, st.Operands())
    ensures st'.GetStack().contents[1..] == st.GetStack().contents[2..]
    ensures forall k:: 2 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k - 1)
    ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 1)

    ensures st'.WritesPermitted() == st.WritesPermitted()
    ensures st'.PC() == st.PC() + 1
  {
    Bytecode.Exp(st)
  }

  function {:opaque} And(st: ExecutingState): (st': ExecutingState)
    requires st.Operands() >= 2
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() - 1
    ensures st'.Capacity() == st.Capacity() + 1
    ensures forall k:: 2 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k - 1)
    ensures forall k:: 1 <= k < st'.Operands() ==> st'.Peek(k) == st.Peek(k + 1)

    ensures st'.GetStack().contents[1..] == st.GetStack().contents[2..]

    // ensures st'.SlicePeek(1, st'.Operands()) == st.SlicePeek(2, st.Operands())
    ensures st'.WritesPermitted() == st.WritesPermitted()
    ensures st'.PC() == st.PC() + 1
  {
    Bytecode.And(st)
  }

  function {:opaque} Address(st: ExecutingState): (st': ExecutingState)
    requires st.Capacity() >= 1
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() + 1
    ensures st'.Capacity() == st.Capacity() - 1

    ensures forall k:: 0 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k + 1)

    ensures st'.GetStack().contents[1..] == st.GetStack().contents
    // ensures st'.SlicePeek(1, st'.Operands()) == st.GetStack()
    ensures st'.PC() == st.PC() + 1
    ensures st'.WritesPermitted() == st.WritesPermitted()

  {
    Bytecode.Address(st)
  }

  /**
    * Get caller address.
    */
  function {:opaque} Caller(st: ExecutingState): (st': ExecutingState)
    requires st.Capacity() >= 1
    ensures st'.EXECUTING?
    ensures st'.Operands() == st.Operands() + 1
    ensures st'.Capacity() == st.Capacity() - 1

    ensures forall k:: 0 <= k < st.Operands() ==> st.Peek(k) == st'.Peek(k + 1)
    ensures st'.GetStack().contents[1..] == st.GetStack().contents
    ensures st'.PC() == st.PC() + 1
    ensures st'.WritesPermitted() == st.WritesPermitted()

    // ensures st'.SlicePeek(1, st'.Operands()) == st.GetStack()
  {
    Bytecode.Caller(st)
  }

}
