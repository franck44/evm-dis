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

// include "./MiscTypes.dfy"
// include "./int.dfy"

/** 
  * Provides finitie automata.
  */
module PartitionMod {

  //   import opened MiscTypes

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
    function {:tailrecursion true} Split(f: nat -> bool): seq<set<nat>> // (p': Partition)
      requires this.IsValid()
    {
      //  Split elem[0] according to value of f for its elements
      if |elem| == 0 then []
      else
        // var setAsSeq := SetToSequence(elem[0]);
        // elem
        var r := SplitSet(elem[0], f);
        [r.0, r.1] +  elem[1..]
    }

  }

  /**
    *   Split a set into two subsets X and Y such that X = f^-1(true) and Y = f^-1(false)
    */
  function SplitSet(xs: set<nat>, f: nat -> bool): (r: (set<nat>, set<nat>))
    ensures xs == r.0 + r.1
  {
    var asSeq := SetToSequence(xs);
    SplitSeq(asSeq, f)
  }

  /**
    *   Split a sequence of nat according to a function value f.
    */
  function {:tailrecursion true} SplitSeq(xs: seq<nat>, f: nat -> bool, cTrue: set<nat> := {}, cFalse: set<nat> := {}, index: nat := 0): (r: (set<nat>, set<nat>))
    requires index <= |xs|
    requires  forall k:: k in xs[..index] <==> k in cTrue + cFalse

    ensures  forall k:: k in xs <==> k in r.0 + r.1

    decreases |xs| - index
  {
    if |xs| == index then (cTrue, cFalse)
    else if f(xs[index]) then
      //   assert forall k:: k in xs[..index] <==> k in cTrue + cFalse
      assert xs[..index + 1] == xs[..index] + [xs[index]];
      SplitSeq(xs, f, cTrue + {xs[index]}, cFalse, index + 1)
    else
      assert !f(xs[index]);
      assert xs[..index + 1] == xs[..index] + [xs[index]];
      SplitSeq(xs, f, cTrue, cFalse + {xs[index]}, index + 1)
  }

  /**
    *   Union of a seq of sets.
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

  /**
    *   Intersection of a seq of sets.
    */
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

  //  Helpers

  /**
    *   Iterate over sets. 
    *   @link{https://leino.science/papers/krml275.html}
    */
  function {:tailrecursion true} SetToSequence(s: set<nat>): (r: seq<nat>)
    ensures forall i :: i in s <==> i in r
  {
    if s == {} then []
    else
      ThereIsAMinimum(s);
      var x :| x in s && forall y :: y in s ==> x <= y;
      [x] + SetToSequence(s - {x})
  }

  /**
    *   @link{https://leino.science/papers/krml275.html}
    */
  lemma ThereIsAMinimum(s: set<nat>)
    requires s != {}
    ensures exists x :: x in s && forall y :: y in s ==> x <= y
  {
    var x :| x in s;
    if s == {x} {
    } else {
      var s' := s - {x};
      assert s == s' + {x};
      ThereIsAMinimum(s');
    }
  }

  method {:test} Test1() {
    var p1 := Partition(4, [set q | 0 <= q < 4]);
    PrintPartition(p1);
    var p2 := p1.Split((x => x % 2 == 0));
    PrintPartition(Partition(4, p2));
  }

  method {:tailrecursion true} PrintPartition(p: Partition)
  {
    for k := 0 to |p.elem| {
      var setToSeq := SetToSequence(p.elem[k]);
      print setToSeq, "\n";
    }
  }

}