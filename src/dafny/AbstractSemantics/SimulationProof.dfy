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

  lemma SimulationCorrectnessStackOp(s: EState, n: nat, k: nat, st: ExecutingState)
    requires s.Abstracts(st) 
    ensures Bytecode.Pop(st).EXECUTING? ==> Pop.requires(s) && Pop(s).Abstracts(Bytecode.Pop(st))
    ensures k > 0 && Bytecode.Dup(st, k).EXECUTING? ==> Dup.requires(s, k) && Dup(s, k).Abstracts(Bytecode.Dup(st, k))
    ensures 1 <= k <= 16 && Bytecode.Swap(st, k).EXECUTING? ==> Swap.requires(s, k) && Swap(s, k).Abstracts(Bytecode.Swap(st, k))
  {   //  Thanks Dafny
  }

  lemma SimulationCorrectnessMemOp(s: EState, n: nat, k: nat, st: ExecutingState)
    requires s.Abstracts(st)
    ensures Bytecode.MLoad(st).EXECUTING? ==> MLoad.requires(s) && MLoad(s).Abstracts(Bytecode.MLoad(st))
    ensures Bytecode.MStore(st).EXECUTING? ==> MStore(s).Abstracts(Bytecode.MStore(st))
  {   //  Thanks Dafny
  }

 
}
