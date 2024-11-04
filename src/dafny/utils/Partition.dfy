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

include "./SeqOfSets.dfy"
include "./MiscTypes.dfy"

/** 
  * Provides partitions of sets of integers of the form {0, ..., n}.
  */
module {:disableNonlinearArithmetic} PartitionMod {

  import opened SeqOfSets
  import opened MiscTypes

  /** A Valid partition. */
  type ValidPartition = x: Partition | x.IsValid() witness MakeInit(1)

  /**
    *   Generate the trivial and valid partition of {0, ..., n - 1}.
    *   @param  n   The size of the set to partition.
    *   @return     A valid partition of {0, ..., n - 1} with a single class
    *               containing all the elements.    
    */
  function {:opaque} MakeInit(n: nat): (p: Partition)
    requires n > 0
    ensures p.IsValid()
    ensures |p.elem| == 1
    ensures p.n == n
  {
    var s := set q {:nowarn} | 0 <= q < n;
    assert {0} <= s;
    reveal_SetU();
    assert SetN([s], n);
    Partition(n, [s])
  }

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
      * must be satisfied:
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
      *  Split an trivial partition (one class) into two partitions.
      *  @param  f   A predicate on the elements of the set.
      *  @returns    A valid partition of {0, ..., n - 1} with at most two classes.
      */
    function SplitIn2(f: nat -> bool): (p': Partition)
      requires this.IsValid()
      requires |elem| == 1
      ensures p'.IsValid()
      ensures |p'.elem| <= 2
      ensures p'.n == n
    {
      reveal_SetU();
      var sTrue := set q | q in SetU(elem) && f(q);
      var sFalse :=  SetU(elem) - sTrue;
      assert SetU(elem) != {};
      assert sTrue != {} || sFalse != {};
      var d := (if sTrue != {} then [sTrue] else []) + (if sFalse != {} then [sFalse] else []);
      var e := this.(elem := d);
      assert sTrue + sFalse == SetU([sTrue]) + SetU([sFalse]);
      assert SetU(d) == sTrue + sFalse;
      assert e.IsValid();
      e
    }

    /**
      *  Compute the finest partition of {0, ..., n - 1} that is consistent with equiv.
      *  @param  equiv  The equivalence relation.
      *  @returns       A valid partition of {0, ..., n - 1} that is consistent with equiv.
      *  @note          The finest partition is the partition with the largest number of classes.
      */
    function {:timeLimitMultiplier 4} {:opaque} ComputeFinest(equiv: (nat, nat) --> bool): (p' :ValidPartition)
      requires this.IsValid()
      requires |elem| == 1
      requires forall x,y:: 0 <= x < n && 0 <= y < n ==> equiv.requires(x, y)
      requires IsEquivRel(equiv, n)

      ensures forall i:: 0 <= i < |p'.elem| ==> forall y:: y in p'.elem[i]  ==> y < n
      ensures p'.n == this.n
      ensures AllClassesAreEquiv(p'.elem, equiv, n)
      ensures DisjointClassesAreNonEquiv(p'.elem, equiv, n)
    {
      SizeOfNatsUpToNBound(n, SetU(elem));
      var k := SplitTrueAndFalse(SetU(elem), equiv, n);
      AllBoundedBy(k, n);
      this.(elem := k)
    }

    /**
      * Refines a given partition with respect to an equivalence relation.
      * @param  equiv  The equivalence relation.
      * @returns       A valid partition of {0, ..., n - 1} that is consistent with equiv.
      */
    function {:timeLimitMultiplier 2} {:opaque} RefineAll(equiv: (nat, nat) --> bool): (p': ValidPartition)
      requires this.IsValid()
      requires forall x,y:: 0 <= x < n && 0 <= y < n ==> equiv.requires(x, y)
      requires IsEquivRel(equiv, n)

      ensures |p'.elem| >= |elem|
      ensures p'.n == n
      ensures p'.IsValid()
    {
      SizeOfNatsUpToNBound(n, SetU(elem));
      var k := SplitAllClasses(elem, equiv, n);
      //    The split preserves some properties
      assert |k| == |elem|;
      assert forall i:: 0 <= i < |k| ==> SetU(k[i]) == elem[i];
      assert forall i:: 0 <= i < |k| ==> AllClassesAreEquiv(k[i], equiv, n);
      assert forall i:: 0 <= i < |k| ==> DisjointClassesAreNonEquiv(k[i], equiv, n);

      //    Now flatten it.
      var d := Flatten(k);
      var e := this.(elem := d);
      //    and prove the validity properties.
      MinSizeOfFlattenForAllNonEmpty(k);
      assert |e.elem| >= |elem|;
      FlattenAllNonEmpty(k, n);
      assert AllNonEmpty(e.elem);
      assert  forall i:: 0 <= i < |k| ==> SetU(k[i]) == elem[i];
      NonFlatDisjointImpliesFlatDisjoint(k, e.elem);
      assert DisjointAnyTwo(e.elem);
      FlattenPreservesSetU(elem, k);
      assert SetU(elem) == SetU(e.elem);
      MaxNumberOfClasses(e.elem, n);
      assert |e.elem| <= n;
      assert e.IsValid();
      e
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
    function {:tailrecursion true} {:opaque} GetClass(x: nat, index: nat := 0): (c: nat)
      requires IsValid()
      requires 0 <= x < n
      requires index < |elem|
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
      *  Get the representative of the class of x.
      *  @param  x   An element in {0, ..., n - 1}.
      *  @returns    The representative of the class of x.
      */
    function {:opaque} GetClassRepOf(x: nat): (c: nat)
      requires IsValid()
      requires 0 <= x < n
      ensures c < n
    {
      var c := GetClass(x);
      SetToSequence(elem[c])[0]
    }

    /**
      * Get the representatives of the classes of a sequence of elements.
      */
    function {:opaque} GetClassRepOfSeqs(xs: seq<nat>): (c: seq<nat>)
      requires IsValid()
      requires forall i:: 0 <= i < |xs| ==> 0 <= xs[i] < n
      ensures |xs| == |c|
      ensures forall i:: 0 <= i < |xs| ==> c[i] < n
    {
      if |xs| == 0 then []
      else [GetClassRepOf(xs[0])] + GetClassRepOfSeqs(xs[1..])
    }
  }

  //    Helpers

  /**
    *   Whether f is an equivalence relation.
    */
  ghost predicate IsEquivRel(f: (nat, nat) --> bool, n: nat)
    requires forall x, y:: 0 <= x < n && 0 <= y < n ==> f.requires(x, y)
  {
    && (forall x:: 0 <= x < n ==> f(x, x))
    && (forall x, x':: 0 <= x < n &&  0 <= x' < n ==> f(x, x') == f(x', x))
    && (forall x, x', x'':: 0 <= x < n &&  0 <= x' < n && 0 <= x'' < n && f(x, x') && f(x', x'') ==> f(x, x''))
  }

  /**
    *   All sets of r are consistent with equiv.
    */
  ghost predicate AllClassesAreEquiv(r: seq<set<nat>>, equiv: (nat, nat) --> bool, n: nat)
    requires forall i, i':: i in r && i' in i ==> i' < n
    requires forall x,y:: 0 <= x < n && 0 <= y < n ==> equiv.requires(x, y)
  {
    forall x, y, y':: x in r && y in x && y' in x ==> equiv(y, y')
  }

  /**
    *    Whether two elements of two distinct sets of r are not equivalent.
    */
  ghost predicate DisjointClassesAreNonEquiv(r: seq<set<nat>>, equiv: (nat, nat) --> bool, n: nat)
    requires forall i, i':: i in r && i' in i ==> i' < n
    requires forall x,y:: 0 <= x < n && 0 <= y < n ==> equiv.requires(x, y)
  {
    forall i, i':: 0 <= i < i' < |r| ==> (forall x, x':: x in r[i] && x' in r[i'] ==> !equiv(x, x'))
  }

  /**
    * Split a set according to a predicate.
    * @param  xs      The set to split.
    * @param  equiv   The equivalence relation.
    * @param  n       The size of the set.
    * @returns        A sequence of sets with some properties.
    * @note           The sequence of sets returned is a partition of xs.
    * @note           The sequence of sets returned is a coarsest partition of xs.
    */
  function {:timeLimitMultiplier 10} {:opaque} {:isolate_assertions} SplitTrueAndFalse(xs: set<nat>, equiv: (nat, nat) --> bool, n: nat): (r :seq<set<nat>>)
    requires forall x::  x in xs ==> x < n
    requires xs != {}
    requires forall x,y:: 0 <= x < n && 0 <= y < n ==> equiv.requires(x, y)
    requires IsEquivRel(equiv, n)

    ensures 1 <= |r| <= |xs|
    ensures SetU(r) == xs
    ensures forall x:: x in SetU(r) ==> x in xs && x < n
    ensures forall i, i':: i in r && i' in i ==> i' < n
    ensures AllNonEmpty(r)
    ensures DisjointAnyTwo(r)
    ensures AllClassesAreEquiv(r, equiv, n)
    ensures DisjointClassesAreNonEquiv(r, equiv, n)
  {
    reveal_SetU();
    var a := SetToSequence(xs);
    var first := SetToSequence(xs)[0];
    var xsTrue := set x: nat | x in xs && equiv(first, x);
    var xsFalse := xs - xsTrue;
    if xsFalse == {} then
      [xsTrue]
    else
      var iter := SplitTrueAndFalse(xsFalse, equiv, n);
      assert AllClassesAreEquiv(iter, equiv, n);
      assert forall x, r1, x':: x in xsTrue && r1 in iter && x' in r1 ==> !equiv(x, x');
      assert DisjointClassesAreNonEquiv(iter , equiv, n);
      assert DisjointClassesAreNonEquiv([xsTrue] + iter , equiv, n);
      [xsTrue] + iter
  }

  /**
    *   Split all the classes of a partition according to a predicate.
    *   @param  xs      The partition to split.
    *   @param  equiv   The equivalence relation.
    *   @param  n       The size of the set.
    *   @returns        A sequence of sets with some good properties.
    */
  function {:opaque} SplitAllClasses(xs: seq<set<nat>>, equiv: (nat, nat) --> bool, n: nat): (r: seq<seq<set<nat>>>)
    requires forall x, i:: x in xs && i in x ==> i < n
    requires AllNonEmpty(xs)
    requires forall x,y:: 0 <= x < n && 0 <= y < n ==> equiv.requires(x, y)
    requires IsEquivRel(equiv, n)
    ensures |r| == |xs|
    ensures forall i:: i in r ==> AllNonEmpty(i) && DisjointAnyTwo(i)
    ensures forall i:: 0 <= i < |r| ==> SetU(r[i]) == xs[i]
    ensures forall i:: 0 <= i < |r| ==> |r[i]| >= 1
    ensures |r| >= |xs|
    ensures forall i:: 0 <= i < |r| ==> forall x:: x in r[i] ==> forall y:: y in x ==> y < n
    ensures forall i:: i in r ==> AllClassesAreEquiv(i, equiv, n)
    ensures forall i:: i in r ==> DisjointClassesAreNonEquiv(i, equiv, n)
  {
    seq(|xs|, i requires 0 <= i < |xs| => SplitTrueAndFalse(xs[i], equiv, n))
  }

  /**
    *   Pretty-print a set.
    */
  method PrintPartition(p: Partition)
  {
    for k := 0 to |p.elem| {
      var setToSeq := SetToSequence(p.elem[k]);
      print setToSeq, "\n";
    }
  }

}