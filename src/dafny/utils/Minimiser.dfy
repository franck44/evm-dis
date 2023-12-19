/*
 * Copyright 2023 Franck Cassez
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

include "./MiscTypes.dfy"
include "./Partition.dfy"
include "./Automata.dfy"
include "./SeqOfSets.dfy"
include "./State.dfy"

/**  
  * Provides minimisation of finite deterministic automata.
  */
abstract module Minimiser {

  import opened MiscTypes
  import opened PartitionMod
  import opened Automata
  import opened SeqOfSets
  import opened State

  type T(!new,==)
  const DEFAULT_STATE: T

  type ValidPair = p: Pair | p.IsValid() witness Pair(Auto().AddState(DEFAULT_STATE), Partition(1, [{0}]))

  function MakeInit(aut: ValidAuto<T>, clazz: ValidPartition): ValidPair
    requires aut.SSize() == clazz.n
    ensures MakeInit(aut, clazz).IsValid()
  {
    Pair(aut, clazz)
  }
  /**    
    *   A pair with an automaton and a partition of its states.
    */
  datatype Pair = Pair(aut: ValidAuto<T>, clazz: ValidPartition) {

    predicate IsValid()
    {
      aut.SSize() == clazz.n
    }

    /**
      * The classes of the true and false successors.
      * @param  x   A state.
      * @returns    A pair of optional successors  (s1, s2) such that 
      *             if x -- true -> xT then s1 is Some(Class(xT)) and None otherwise.
      *             if x -- false -> xFthen s2 is Some(Class(xF)) and None otherwise.
      */
    function ClassSucc(x: nat): seq<nat>
      requires this.IsValid()
      requires x < aut.SSize()
      ensures forall k:: k in ClassSucc(x) ==> k < |clazz.elem|
    {
      var l := aut.SuccNat(x);
      seq(|l|, z requires 0 <= z < |l|=> clazz.GetClass(l[z]))
    }

    function ClassSplitter() : ValidPair
      requires this.IsValid()
    {
      IsEquivRelF();
      this.(clazz := clazz.RefineAll(Splitter))
    }

    function Splitter(x: nat, y: nat): bool
      requires this.IsValid()
      requires x < aut.SSize() && y < aut.SSize()
      ensures Splitter(x, y) <==> ClassSucc(x) == ClassSucc(y)
    {
      ClassSucc(x) == ClassSucc(y)
    }

    function Minimise(): ValidPair
      requires this.IsValid()
    {
      IterSplit(this)
    }
   
    lemma IsEquivRelF()
      requires this.IsValid()
      ensures IsEquivRel(Splitter, aut.SSize())
    {
      //  Thanks Dafny
    }

  }

  //   Helper and Main function.

  /**    
    *   Iterate splitting until nore more splits are possible.
    */
  function IterSplit(pp: ValidPair): ValidPair
    decreases pp.clazz.n - |pp.clazz.elem|
  {
    var p1 := pp.ClassSplitter();
    if |p1.clazz.elem| == |pp.clazz.elem| then pp 
    else IterSplit(p1)
  }

}