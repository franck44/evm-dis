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
module Partition {

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
      && SetUnion(elem) == set q {:notrigger } | 0 <= q < n
    }

    /**
      *  Split a partition according to a predicate
      */
    function Split(f: nat -> bool): (p': Partition)
      requires this.IsValid()
    //   requires p'. n == n
    //   requires p'.IsValid()
      ensures p'.n == n 
      ensures p'.IsValid()
    {
        //  Split elem[0] according to value of f for its elements
      this
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


}