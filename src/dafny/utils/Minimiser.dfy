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

/** 
  * Provides minimisation of finite deterministic automata.
  */
module Minimiser {

  import opened MiscTypes
  import opened PartitionMod
  import opened Automata
  import opened SeqOfSets

  type ValidPair = p: Pair | p.IsValid() witness Pair(Auto(1, map[]), Partition(1, [{0}]))

  /**   
    *   A pair with a an automaton and a partition of its states.
    */
  datatype Pair = Pair(a: ValidAuto, p: ValidPartition) {

    predicate IsValid()
    {
      a.numStates == p.n
    }

    function Auto(): ValidAuto
    {
      a
    }

    function Parts(): ValidPartition
    {
      p
    }

    /**
      * The classes of the true and false successors.
      * @param  x   A state.
      * @returns    A pair of optional successors  (s1, s2) such that 
      *             if x -- true -> xT then s1 is Some(Class(xT)) and None otherwise.
      *             if x -- false -> xFthen s2 is Some(Class(xF)) and None otherwise.
      */
    function ClassSucc(x: nat): (Option<nat>, Option<nat>)
      requires this.IsValid()
      requires x < a.numStates
      ensures ClassSucc(x).0.Some? ==> ClassSucc(x).0.v < |p.elem|
      ensures ClassSucc(x).1.Some? ==> ClassSucc(x).1.v < |p.elem|
    {
      var s1 := match a.Succ(x, false)
        case None => None
        case Some(n) =>
          assert p.GetClass(n) < p.n == a.numStates;
          Some(p.GetClass(n));
      var s2 := match a.Succ(x, true)
        case None => None
        case Some(n) =>
          assert p.GetClass(n) < p.n == a.numStates;
          Some(p.GetClass(n));
      (s1, s2)
    }

    /**
      * Split all classes according to value of first elem of each class.
      * @returns    A pair where each class[index] has been split according to 
      */
    function SplitFrom(): (p' :ValidPair)
      requires this.IsValid()
      ensures p'.IsValid()
      ensures |p'.p.elem| >= |p.elem|
    {
      //  split class[index] with function that is true only
      //  when ClassSucc is the same as ClassSucc[index] first element
      //  Note that this ClassSucc[index] is a set so it is first
      //  enumerated as a sequence in the process.

      //  Partial function to define each class splitter.
      //  This is a bit more tricky than total function but
      //  provides more guarantee e.g. on the value of ClassSucc.
      assert p.n == a.numStates;
      var splitterF: nat --> (nat --> bool) :=
        (k: nat) requires 0 <= k < |p.elem|
        => ((y: nat) requires y < p.n =>
              ClassSucc(SetToSequence(p.elem[k])[0]) == ClassSucc(y));
      var r := SplitAll(p, splitterF);
      this.(p := r)
    }

    /**
      *  for each class in p.elem get the successor classes and create edges. 
      * @note   Tailrecursion is diasbled as there is a bug in the Dafny Java code generator.
      * @link{https://github.com/dafny-lang/dafny/issues/2346} 
      */
    function {:tailrecursion false} GenerateReduced(index: nat := 0): (r : seq<(nat, bool, nat)>)
      requires this.IsValid()
      requires index <= |p.elem|
      ensures forall k:: 0 <= k < |r| ==> r[k].0 < p.n && r[k].2 < p.n
      decreases |p.elem| - index
    {
      AllBoundedBy(p.elem, p.n);
      MaxNumberOfClasses(p.elem, p.n);
      if index == |p.elem| then []
      else
        var firstElem := SetToSequence(p.elem[index])[0];
        //  Get successor classes of first elem
        var succs := ClassSucc(firstElem);
        var newEdges := match (succs.0, succs.1)
          case (None, None) => []
          case (Some(sFalse), None) => [(firstElem, false, SetToSequence(p.elem[sFalse])[0])]
          case (None, Some(sTrue)) => [(firstElem, true, SetToSequence(p.elem[sTrue])[0])]
          case (Some(sFalse), Some(sTrue)) => [(firstElem, false, SetToSequence(p.elem[sFalse])[0]), (firstElem, true, SetToSequence(p.elem[sTrue])[0])]
          ;
        newEdges + GenerateReduced(index + 1)
    }

  }

  //   Helper and Main function.

  /**
    *   Minimise an automaton.
    * @note   Tailrecursion is disabled as there is a bug in the Dafny Java code generator.
    * @link{https://github.com/dafny-lang/dafny/issues/2346} 
    *   
    */
  function {:tailrecursion false} Minimise(ap: ValidPair): ValidPair
    requires ap.IsValid()
    ensures Minimise(ap).IsValid()
    ensures Minimise(ap).p.n == ap.p.n
    decreases ap.p.n - |ap.p.elem|
  {
    assert AllNonEmpty(ap.p.elem);
    var p1 := ap.SplitFrom();
    MaxNumberOfClasses(p1.p.elem, p1.p.n);
    if |p1.p.elem| == |ap.p.elem| then p1
    else
      assert |ap.p.elem| < |p1.p.elem| <= ap.p.n == ap.a.numStates;
      Minimise(p1)
  }

}