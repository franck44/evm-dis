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

    function Split(): ValidPair
      requires this.IsValid()
      ensures Split().IsValid()
      ensures |Split().p.elem| >= |p.elem|
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
        (index: nat) requires index < |p.elem|
        => ((y: nat) requires y < p.n =>  ClassSucc(p.GetClass(SetToSequence(p.elem[index])[0])) == ClassSucc(y));
      assert p.SplitAllFrom.requires(splitterF, 0);
      var r := p.SplitAllFrom(splitterF, 0);
      assert r.IsValid();
      assert r.n == p.n;
      assert r.n == a.numStates;
      var x := this.(p := r);
      assert x.IsValid();
      x
    }

    function Minimise(): ValidPair
      requires this.IsValid()
      ensures Minimise().IsValid()
      decreases this.p.n - |this.p.elem|
    {
      var p1 := this.Split();
      ValidMaxClasses(p1.p);
      assert p1.IsValid();
      if |p1.p.elem| == |p.elem| then p1
      else
        assert |p.elem| < |p1.p.elem| <= p.n == a.numStates;
        p1.Minimise()
    }

    /**
      *  Split a class into element equiv to class[0] and !class[0]
      */

    // function Refine(): ValidPartition
    //   requires this.IsValid()
    // {
    //   p
    // }


    /**  */
    // function SplitSeq(index: nat) : (nat -> bool)
    // {
    //     //  Get first element.
    // }


  }



}