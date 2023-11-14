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
  * Provides minimisation of finite automata.
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
      NotEmpty(p);
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
      * Split classes at index and above according to value of first elem of the class
      * and it successors.
      */
    function SplitFrom(index: nat := 0): ValidPair
      requires this.IsValid()
      requires index < |p.elem|
      ensures SplitFrom(index).IsValid()
      ensures |SplitFrom(index).p.elem| >= |p.elem|
    //   ensures SplitFrom(index).p.elem[..index] == p.elem[..index]
    {
      //  split class[index] with function that is true only
      //  when ClassSucc is the same as ClassSucc[index] first element
      //  Note that this ClassSucc[index] is a set so it is first
      //  enumerated as a sequence in the process.
      AllClassesInSetU(p);
      //  Partial function to define each class splitter.
      //  This is a bit more tricky than total function but
      //  provides more guarantee e.g. on the value of ClassSucc.
      assert p.n == a.numStates;
      var splitterF: nat --> (nat --> bool) :=
        (k: nat) requires index <= k < |p.elem|
        => ((y: nat) requires y < p.n =>  ClassSucc(p.GetClass(SetToSequence(p.elem[k])[0])) == ClassSucc(y));
      assert SplitAllFrom.requires(p, splitterF, index, index);
      var r := SplitAllFrom(p, splitterF, index);
    //   assert r.elem[..index] == p.elem[..index];
      assert r.IsValid();
      assert r.n == p.n;
      assert r.n == a.numStates;
      var x := this.(p := r);
      assert x.IsValid();
      x
    }

    /**
     for each class in p.elem get the successor classes and create edges. 
     */
    function GenerateReduced(index: nat := 0): (r : seq<(nat, bool, nat)>)
      requires this.IsValid()
      requires index <= |p.elem|
      ensures forall k:: 0 <= k < |r| ==> r[k].0 < p.n && r[k].2 < p.n
      decreases |p.elem| - index 
    {
      AllClassesInSetU(p);
      ValidMaxClasses(p);
      if index == |p.elem| then []
      else
        // assert p.elem[index] != {};
        var firstElem := SetToSequence(p.elem[index])[0];
        // assert firstElem in p.elem[index];
        // assert firstElem < a.numStates;
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

    /**
      * 
      */
    function Minimise1(): ValidPair
      requires this.IsValid()
      ensures Minimise1().IsValid()
    //   ensures 
      decreases this.p.n - |this.p.elem|
    {
      NotEmpty(p);
      var p1 := this.SplitFrom();
      ValidMaxClasses(p1.p);
      if |p1.p.elem| == |p.elem| then p1
      else
        assert |p.elem| < |p1.p.elem| <= p.n == a.numStates;
        p1.Minimise1()
    }

  }

  //   function

  function Minimise(ap: ValidPair): ValidPair
    requires ap.IsValid()
    ensures Minimise(ap).IsValid()
    ensures Minimise(ap).p.n == ap.p.n
    decreases ap.p.n - |ap.p.elem|
  {
    NotEmpty(ap.p);
    var p1 := ap.SplitFrom();
    ValidMaxClasses(p1.p);
    if |p1.p.elem| == |ap.p.elem| then p1
    else
      assert |ap.p.elem| < |p1.p.elem| <= ap.p.n == ap.a.numStates;
      Minimise(p1)
  }


}