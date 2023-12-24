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

/**  
  * Provides minimisation of finite deterministic automata of type T.
  * @param  T   The type of the states of the automaton.
  * @note       The type must support equality, not be a reference type, and have   
  */
abstract module Minimiser {

  import MiscTypes
  import opened PartitionMod
  import opened Automata

  /**
    * The type of the states of the automaton and a default state.
    */
  type T(!new,==)
  const DEFAULT_STATE: T

  /**
    *  A valid automaton is an automaton that satisfies the IsValid predicate.
    *   i.e. the size of the automaton is the same as the sie pf the partition.
    */
  type ValidPair = p: Pair | p.IsValid() witness Pair(Auto().AddState(DEFAULT_STATE), Partition(1, [{0}]))

  /**
    *  Make a valid pair from an automaton and a partition.
    *  @param  aut     An automaton.
    *  @param  clazz   A partition.
    *  @returns        A valid pair with aut, clazz.
    */
  function MakeInit(aut: ValidAuto<T>, clazz: ValidPartition): ValidPair
    requires aut.SSize() == clazz.n
    ensures MakeInit(aut, clazz).IsValid()
  {
    Pair(aut, clazz)
  }

  /**    
    *   A pair is an automaton and a partition of its states.
    */
  datatype Pair = Pair(aut: ValidAuto<T>, clazz: ValidPartition) {

    /** A valid Pair must have compatible sizes.
      *  Each stateId of the automaton must be in the range of the partition.
      *  @returns  True if and only if the sizes are compatible.
      */
    ghost predicate IsValid()
    {
      aut.SSize() == clazz.n
    }

    /**
      * The classes of the true and false successors.
      * @param  x   A state.
      * @returns    The successor classes of x.
      */
    function {:opaque} ClassSucc(x: nat): seq<nat>
      requires this.IsValid()
      requires x < aut.SSize()
      ensures forall k:: k in ClassSucc(x) ==> k < |clazz.elem|
    {
      var l := aut.SuccNat(x);
      seq(|l|, z requires 0 <= z < |l|=> clazz.GetClass(l[z]))
    }

    /**
      *  Split all classes according to the class splitter relation.
      */
    function {:opaque} ClassSplitter() : (p': ValidPair)
      requires this.IsValid()
      ensures p'.clazz.n == this.clazz.n
      ensures p'.aut == this.aut
      ensures |p'.clazz.elem| >= |this.clazz.elem|
    {
      IsEquivRelF();
      this.(clazz := clazz.RefineAll(Splitter))
    }

    /**
      *  The splitter relation.
      *  @param     x   A stateId.
      *  @param     y   A stateId.
      *  @returns   True if and only if class successors of the 
      *              two states are equal.
      */
    function {:opaque} Splitter(x: nat, y: nat): bool
      requires this.IsValid()
      requires x < aut.SSize() && y < aut.SSize()
      ensures Splitter(x, y) <==> ClassSucc(x) == ClassSucc(y)
    {
      ClassSucc(x) == ClassSucc(y)
    }

    /**
      *  Minimise the automaton.
      *  @returns  The minimised automaton.
      */
    function {:opaque} Minimise(): (a: ValidAuto<T>)
      requires this.IsValid()
      ensures forall s:: s in a.states ==> s in this.aut.states
    {
      //  Compute fix point of splitter relation
      var p1 := IterSplit(this);
      assert p1.aut == this.aut;
      //  Compute the new automaton
      p1.MapToClasses()

    }

    /**
      *  Make sure that the splitter relation is an equivalence relation.
      */
    lemma IsEquivRelF()
      requires this.IsValid()
      ensures IsEquivRel(Splitter, aut.SSize()) 
    {
      //  Thanks Dafny
    }

    /** Map an automaton to a new automaton.
      * @param  acc     The accumulator automaton.
      * @param  index   The index of the state to be processed.      
      * @returns  The new automaton.
      */
    function {:timeLimitMultiplier 3} {:opaque} MapToClasses(acc: ValidAuto<T> := Auto(), index: nat := 0): (r: ValidAuto<T>)
      requires this.IsValid()
      requires index <= |aut.states|
      requires forall s:: s in acc.states ==> s in this.aut.states
      ensures forall s:: s in r.states ==> s in this.aut.states
      decreases |aut.states| - index
    {
      if index == |aut.states| then acc
      else
        var succs := MiscTypes.MapP(clazz.GetClassRepOfSeqs(aut.transitionsNat[index]), (i: nat) requires 0 <= i < aut.SSize() => aut.states[i]);
        var a' := MapToClasses(acc.AddEdges(aut.states[clazz.GetClassRepOf(index)], succs), index + 1);
        a'
    }

    //  Helpers

    /**    
      *   Iterate refining until no more splits are possible.
      */
    static function {:opaque} IterSplit(pp: ValidPair): (r: ValidPair)
      ensures r.aut == pp.aut
      decreases pp.clazz.n - |pp.clazz.elem|
    {
      var p1 := pp.ClassSplitter();
      if |p1.clazz.elem| == |pp.clazz.elem| then pp
      else IterSplit(p1)
    }
  }



}