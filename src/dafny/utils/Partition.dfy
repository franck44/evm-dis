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
include "./int.dfy"

/** 
  * Provides finitie automata.
  */
module PartitionMod {

  import opened MiscTypes


  // function Refine(p: Partition): Partition
  //   requires p.IsValid()
  // //   requires p.n == |states|
  // //   ensures Refine(p).n == |states|
  //   ensures Refine(p).IsValid()
  //     // ensures Refine(p).IsRefinement(p)
  // {
  //   p
  // }


  /**
    *   A partition is a list of sets but we represent them by seq to 
    *   be able to iterate.
    *   Partitions of {0, ... n - 1}
    */
  datatype Partition = Partition(n: nat, elem: seq<set<nat>>)
  {
    /**
      * A valid partition should map every nat to a partition number.
      * The maximum number of classes is n (each element has its own class).
      */
    ghost predicate IsValid()
    {
      && (forall k, k':: 0 <= k < k' < |elem| ==> elem[k] * elem[k'] == {})
      && SetUnion(elem) == set q | 0 <= q < n
    }

    /**
      *  Split a partition according to a predicate
      */
    function Split(f: nat -> bool): seq<set<nat>> // (p': Partition)
      requires this.IsValid()
    {
      //  Split elem[0] according to value of f for its elements
      if |elem| == 0 then []
      else
        var setAsSeq := SetToSequence(elem[0]);
        // elem
        var r := SplitSeq(setAsSeq, f);
        [r.0, r.1] +  elem[1..]
    }

  }

  function SplitSeq(xs: seq<nat>, f: nat -> bool, cTrue: set<nat> := {}, cFalse: set<nat> := {}): (set<nat>, set<nat>)
  {
    if |xs| == 0 then (cTrue, cFalse)
    else
    if f(xs[0]) then
      SplitSeq(xs[1..], f, cTrue + {xs[0]}, cFalse)
    else
      assert !f(xs[0]);
      SplitSeq(xs[1..] , f, cTrue, cFalse + {xs[0]})
  }

  function SetToSequence(s: set<nat>): seq<nat>
    ensures var q := SetToSequence(s);
            forall i :: 0 <= i < |q| ==> q[i] in s
  {
    if s == {} then []
    else
      ThereIsAMinimum(s);
      var x :| x in s && forall y :: y in s ==> x <= y;
      [x] + SetToSequence(s - {x})
  }

  lemma ThereIsAMinimum(s: set<nat>)
    requires s != {}
    ensures exists x :: x in s && forall y :: y in s ==> x <= y
  {
    var x :| x in s;
    if s == {x} {
      // obviously, x is the minimum
    } else {
      // The minimum in s might be x, or it might be the minimum
      // in s - {x}. If we knew the minimum of the latter, then
      // we could compare the two.
      // Let's start by giving a name to the smaller set:
      var s' := s - {x};
      // So, s is the union of s' and {x}:
      assert s == s' + {x};
      // The following lemma call establishes that there is a
      // minimum in s'.
      ThereIsAMinimum(s');
    }
  }


  /**
    *   Union of sets.
    */
  function {:tailrecursion true} SetUnion<T>(xs: seq<set<T>>, c: set<T> := {}, index: nat := 0): (r: set<T>)
    requires index <= |xs|
    requires forall k:: 0 <= k < index ==> xs[k] <= c
    requires forall e:: e in c ==> exists k:: 0 <= k < index && e in xs[k]

    ensures forall k:: k in xs ==> k <= r
    ensures forall e:: e in r ==> exists k:: 0 <= k < |xs| && e in xs[k]
    decreases |xs| - index
  {
    if |xs| == index then c
    else
      SetUnion(xs, c + xs[index], index + 1)
  }

  function {:tailrecursion true} SetIntersection<T(!new)>(xs: seq<set<T>>, c: set<T> := {}, index: nat := 0): (r: set<T>)
    requires index <= |xs|
    requires forall k:: 0 <= k < index ==> c <= xs[k]
    requires forall e:: e in c ==> forall k:: 0 <= k < index && e in xs[k]
    requires forall e:: (forall k:: 0 <= k < index ==> e in xs[k]) ==> e in c

    ensures forall k:: k in xs ==> r <= k
    ensures forall e:: e in r ==> (forall k:: 0 <= k < |xs| ==> e in xs[k])
    ensures forall e:: (forall k:: 0 <= k < |xs| ==> e in xs[k]) ==> e in r
    decreases |xs| - index
  {
    if |xs| == index then c
    else
      SetIntersection(xs, c * xs[index], index + 1)
  }

  method {:test} Test1() {
    var p1 := Partition(4, [set q | 0 <= q < 4]);
    PrintPartition(p1);
    var p2 := p1.Split((x => x % 2 == 0));
    PrintPartition(Partition(4, p2));
  }

  method PrintPartition(p: Partition) 
  {
    for k := 0 to |p.elem| {
        var setToSeq := SetToSequence(p.elem[k]);
        print setToSeq, "\n";
    }
  }

}