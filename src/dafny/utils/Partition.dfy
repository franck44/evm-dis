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

include "./SeqOfSets.dfy"
include "./MiscTypes.dfy"

/** 
  * Provides partitions of sets of the form {0, ..., n}.
  */
module PartitionMod {

  import opened SeqOfSets
  import opened MiscTypes

  /** A Valid partition. */
  type ValidPartition = x: Partition | x.IsValid() witness Partition(1, [{0}])

  /**
    *   A partition is a list of sets and we represent it by a seq of sets to 
    *   be able to iterate over it.
    *   Partitions of {0, ... n - 1}
    */
  datatype Partition = Partition(n: nat, elem: seq<set<nat>>)
  {
    /**
      * A valid partition should map every nat to a partition number.
      * We consider only partition of non empty sets {0, ..., n} and 
      *     0. requires n > 0.
      * For a seq<set<nat>> to be partition of {0, .., n - 1} the following properties
      * must ne satisfied:
      *     1. each class (set) in the partition is non empty
      *     2. the intersection of two distinct classes is empty
      *     3. the union of the classes is the whole set {0, .., n - 1}
      *     4. The maximum number of classes is n (each element has its own class).
      */
    ghost predicate IsValid()
    {
      && n > 0
      && AllNonEmpty(elem)
      && DisjointAnyTwo(elem)
      && SetN(elem, n)
      && 0 < |elem| <= n
    }

    /**
      * Split all the classes according to a predicate.
      * @param  f       A boolean splitter function f(index) for each index.
      * @param  index   The current class to split according to f.
      * @returns        Splits each class C_1, C_2, C_k into C_1_True, C_1_False
      *                 C_2_True, C_2_False etc. Remove empty classes and returns 
      *                 a Valid partition. 
      */
    // function {:tailrecursion true} {:timeLimitMultiplier 8} SplitAllFrom2(f: nat --> nat --> bool, index: nat := 0, ghost from: nat := index): (p': ValidPartition)
    //   requires this.IsValid()
    //   requires from <= index <= |elem|
    //   requires forall x:nat :: index <= x < |elem| ==> f.requires(x)
    //   requires forall x :: index <= x < |elem| ==> (forall y:nat :: y < n ==> f(x).requires(y))
    //   requires forall x:nat :: index <= x < |elem| ==> (forall y:nat:: y in elem[x] ==> f(x).requires(y))
    //   decreases |elem| - index
    //   ensures p'.IsValid()
    //   ensures |p'.elem| >= |elem|
    //   ensures p'.elem[..from] == elem[..from]
    //   ensures p'.n == n
    // {
    //   if |elem| == index then this
    //   else
    //     var p1 := SplitAt(f(index), index);
    //     //  We may add one or zero sets depending on whether splitting elem[index]
    //     //  results in one empty set. If we get one set we advance to index + 1 and
    //     //  if we get two we advance to index + 2
    //     //  We have so shift f too
    //     var f': nat --> nat --> bool := (x:nat) requires index + 1 <= x < |p1.elem| => f(x - (|p1.elem| - |elem|));
    //     assert p1.elem[..from] == elem[..from];
    //     p1.SplitAllFrom2(f', index + 1 + |p1.elem| - |elem|, from)
    // }

    /**
      * Split a partition according to a predicate.
      * @param  f       A boolean splitter function.
      * @param  index   The class to split according to f.
      * @returns        p with the class C at index split into cTrue and CFalse 
      *                 where CTrue = { c in C | f(c) = true} (and similar for false).
      * @note           C is not empty but the split can create an empty e.g. if 
      *                 forall c in C f(c). The result discards any empty sets 
      *                 and returns a ValidPartition. 
      * @note           The last 2 classes agree on the value of f for each of their elements.
      */
    function {:tailrecursion true} SplitAt(f: nat --> bool, index: nat): (p': ValidPartition)
      requires index < |elem|
      requires this.IsValid()
      requires forall x:: 0 <= x < n ==> f.requires(x)
      ensures p'.IsValid()
      ensures |elem| <= |p'.elem| <= |elem| + 1
      ensures p'.n == n
      ensures |elem| == |p'.elem| ==> p'.elem[|p'.elem| - 1] == elem[index]
      //  needed to establish the last 2
      ensures forall x:: x in p'.elem[|elem| - 1] ==> f.requires(x)
      ensures forall x:: x in p'.elem[|p'.elem| - 1] ==> f.requires(x)
      ensures forall e, e':: e in p'.elem[|elem| - 1] && e' in p'.elem[|elem| - 1] ==> f(e) == f(e')
      ensures forall e, e':: e in p'.elem[|p'.elem| - 1] && e' in p'.elem[|p'.elem| - 1] ==> f(e) == f(e')
      //   ensures p'.Refines2(this)
    {
      // Split elem[index] according to value of f for its elements
      // each class is non empty including elem[index]
      assert AllNonEmpty(elem);
      // elem[index] <= 0 .. n and f is defined on elem[index]
      AllBoundedBy(elem, n);
      var r := SplitSet(elem[index], f);
      assert elem[index] == r.0 + r.1 != {} && r.0 * r.1 == {};

      //  Append new classes at the end and remove elem[index]
      if r.0 != {} && r.1 != {} then
        var j := elem[..index] + elem[index + 1..] + [r.0, r.1];
        calc == {
          SetU([r.0, r.1]);
          SetU([r.0]) + SetU([r.1]);
          r.0 + r.1;
          elem[index];
        }
        PermutePreservesUnionG(elem, index, [r.0, r.1]);
        MaxNumberOfClasses(j, n);
        var pp := Partition(n, j);
        // assert pp.elem[..index] == elem[..index];
        // assert pp.elem[index..|j| - 2] == elem[index + 1..];
        // assert pp.elem[|j| - 2] == r.0;
        // assert pp.elem[|j| - 1] == r.1;
        // assert (forall k |  k in pp.elem
        //     ensures forall k:: k in pp.elem ==> exists c:: c in p.elem && k <= c
        //     {

        // });
        // assert pp.Refines2(this);
        pp
      else if r.0 != {} then
        var j := elem[..index] + elem[index + 1..] + [r.0];
        assert |j| == |elem| <= n;
        PermutePreservesUnionG(elem, index, [r.0]);
        Partition(n, j)
      else
        var j := elem[..index] + elem[index + 1..] + [r.1];
        assert |j| == |elem| <= n;
        PermutePreservesUnionG(elem, index, [r.1]);
        Partition(n, j)
    }

    /**
      * The class (index) of an element in {0, ..., n - 1}.
      *
      * @param  x       An element in {0, ..., n - 1}.
      * @param  index   The next index to scan and x !in p.elem[..index].
      * @returns        The index of the class x is in.
      * @note           Because each x is necessarily in a class we always return 
      *                 an index in p.elem.
      */
    function {:tailrecursion true} GetClass(x: nat, index: nat := 0): (c: nat)
      requires IsValid()
      requires 0 <= x < n
      requires index < |elem|
      //    index has not been found yet
      requires forall k:: 0 <= k < index ==> x !in elem[k]
      ensures c < |elem| <= n && x in elem[c]
      decreases |elem| - index
    {
      // This lemma ensures we will find an index with x in elem[index]!
      LessThanNIsInAClass(elem, n, x);
      assert exists i:: 0 <= i < |elem| && x in elem[i];
      if x in elem[index] then index
      else GetClass(x, index + 1)
    }

    /**
      * Whether two nats are equivalemt i.e. in the same class.
      */
    predicate Equiv(x: nat, y: nat)
      requires this.IsValid()
      requires 0 <= x < n
      requires 0 <= y < n
      //   ensures Equiv(x, y) ==> exists k:: 0 <= k < |elem| && x in elem[k] && y in elem[k]
      ensures x == y ==> Equiv(x, y)
    {
      assert GetClass(x) == GetClass(y) ==> x in elem[GetClass(x)] && y in elem[GetClass(y)];
      GetClass(x) == GetClass(y)
    }

    predicate Refines2(p: Partition)
      requires IsValid()
      requires p.IsValid()
      requires p.n == n
    {
      forall k:: k in elem ==> exists c:: c in p.elem && k <= c
    }

    /**
      * Whether this refines p.
      */
    predicate Refines(p: Partition)
      requires IsValid()
      requires p.IsValid()
      requires p.n == n
      // ensures Refines(p) ==> |elem| >= |p.elem|
    {
      && |elem| >= |p.elem|
      //   && (forall x, x':: 0 <= x < x' < n ==> (Equiv(x, x') ==> p.Equiv(x, x')))
    }
  }

  // in the SplitAll, f must be applied to all the values so must be a total function
  function {:tailrecursion true} SplitAll(p: ValidPartition, f : nat --> nat --> bool, index: nat := 0, max : nat := |p.elem|): (p': ValidPartition)
    requires p.IsValid()
    requires index <= max
    requires forall x:: 0 <= x < max - index ==> f.requires(x)
    requires forall x:: 0 <= x < max - index ==>  f.requires(x) && (forall y:: 0 <= y < p.n ==> f(x).requires(y))
    ensures p'.IsValid()
    ensures |p'.elem| >= |p.elem|
    ensures p'.n == p.n
    decreases max - index
  {
    if max == index then p
    else
      assert |p.elem| > 0;
      AllBoundedBy(p.elem, p.n);
      var f' : nat --> nat --> bool := (x: nat) requires 0 <= x < max - (index + 1) => f(x + 1);
      var p1 := p.SplitAt(f(0), 0);
      SplitAll(p1, f', index + 1, max)
  }

  //  Helper lemma

  /**
    *   Replacing xs[i] by a seq that has the same elements 
    *   preservers the union.
    */
  lemma PermutePreservesUnionG(xs: seq<set<nat>>, i: nat, xs2: seq<set<nat>>)
    requires 0 <= i < |xs|
    requires SetU(xs2) == xs[i]
    requires 0 <= i < |xs|
    ensures SetU(xs[..i] + xs[i + 1..] + xs2) == SetU(xs)
  {
    calc == {
       SetU(xs[..i] + xs[i + 1..] + xs2);
      { DistribUnion3(xs[..i], xs[i + 1..], xs2) ; }
       SetU(xs[..i]) + SetU(xs[i + 1..]) + SetU(xs2) ;
    == SetU(xs[..i]) + SetU(xs[i + 1..]) + xs[i];
      calc == {
        xs[i];
        SetU([xs[i]]);
      }
       SetU(xs[..i]) + SetU(xs[i + 1..]) + SetU([xs[i]]);
       SetU(xs[..i])  + SetU([xs[i]]) + SetU(xs[i + 1..]);
      { DistribUnion3(xs[..i], [xs[i]], xs[i + 1..]) ; }
       SetU(xs[..i] + [xs[i]] + xs[i + 1..]);
      calc == {
        xs[..i] + [xs[i]] + xs[i + 1..];
        xs;
      }
       SetU(xs);
    }
  }

  /**
    *   Pretty print a set.
    */
  method {:tailrecursion true} PrintPartition(p: Partition)
  {
    for k := 0 to |p.elem| {
      var setToSeq := SetToSequence(p.elem[k]);
      print setToSeq, "\n";
    }
  }

}