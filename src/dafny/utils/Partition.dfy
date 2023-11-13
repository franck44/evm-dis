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

  /** A Avlid partition. */
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
      * The maximum number of classes is n (each element has its own class).
      */
    ghost predicate IsValid()
    {
      && n > 0
      && (forall k:: 0 <= k < |elem| ==> {} != elem[k])
      && (forall k, k':: 0 <= k < k' < |elem| ==> elem[k] * elem[k'] == {})
      && SetU(elem) == set q {:nowarn} | 0 <= q < n
    }

    /**
      * Split all the classes according to a predicate.
      * @param  f       A boolean splitter function f(index) for each index.
      * @param  index   The current class to split according to f.
      * @returns        Splits each class C_1, C_2, C_k into C_1_True, C_1_False
      *                 C_2_True, C_2_False etc. Remove empty classes and returns 
      *                 a Valid partition. 
      */
    function {:tailrecursion true} {:timeLimitMultiplier 8} SplitAllFrom2(f: nat --> nat --> bool, index: nat := 0, ghost from: nat := index): (p': ValidPartition)
      requires this.IsValid()
      requires from <= index <= |elem|
      requires forall x:nat :: index <= x < |elem| ==> f.requires(x)
      requires forall x :: index <= x < |elem| ==> (forall y:nat :: y < n ==> f(x).requires(y))
      requires forall x:nat :: index <= x < |elem| ==> (forall y:nat:: y in elem[x] ==> f(x).requires(y))
      decreases |elem| - index
      ensures p'.IsValid()
      ensures |p'.elem| >= |elem|
      ensures p'.elem[..from] == elem[..from]
      ensures p'.n == n
    {
      if |elem| == index then this 
      else
        var p1 := SplitAt(f(index), index);
        //  We may add one or zero sets depending on whether splitting elem[index]
        //  results in one empty set. If we get one set we advance to index + 1 and
        //  if we get two we advance to index + 2
        //  We have so shift f too
        var f': nat --> nat --> bool := (x:nat) requires index + 1 <= x < |p1.elem| => f(x - (|p1.elem| - |elem|));
        assert p1.elem[..from] == elem[..from];
        p1.SplitAllFrom2(f', index + 1 + |p1.elem| - |elem|, from)
    }

    /**
      * Split a partition according to a predicate.
      * @param  f       A boolean splitter function.
      * @param  index   The class to split according to f.
      * @returns        p with the class C at index split into cTrue and CFalse 
      *                 where CTrue = { c in C | f(c) = true} (and similar for false).
      * @note           C is not empty but the split can create an empty e.g. if 
      *                 forall c in C f(c). The result discards any empty sets 
      *                 and returns a ValidPartition. 
      */
    function {:tailrecursion true} {:timeLimitMultiplier 4} SplitAt(f: nat --> bool, index: nat): (p': ValidPartition)
      requires index < |elem|
      requires this.IsValid()
      requires forall x:: x in elem[index] ==> f.requires(x)
      ensures p'.IsValid()
      ensures |elem| + 1 >= |p'.elem| >= |elem|
      ensures p'.elem[..index] == elem[..index]
      ensures p'.n == n
    {
      //  Split elem[index] according to value of f for its elements
      assert forall x:: x in elem[index] ==> f.requires(x);
      var r := SplitSet(elem[index], f);
      assert elem[index] != {};
      assert r.0 != {} || r.1 != {};
      var newP := elem[..index] + [r.0, r.1] + elem[index + 1..];
      assert (forall k, k':: 0 <= k < k' < |elem| ==> elem[k] * elem[k'] == {});
      assert (forall k :: 0 <= k < |elem| ==> k != index ==> elem[k] * elem[index] == {});
      assert (forall k :: 0 <= k < |elem| ==> k != index ==> elem[k] * r.0 == {});
      assert (forall k :: 0 <= k < |elem| ==> k != index ==> elem[k] * r.1 == {});
      assert (forall k, k':: 0 <= k < k' < |newP| ==> newP[k] * newP[k'] == {});
      assert r.0 + r.1 == elem[index];
      calc == {
        SetU(newP);
        { SplitUnion2(newP, index); }
        SetU(newP[..index] )+ newP[index] + newP[index + 1] +  SetU(newP[index + 2..]);
        { assert newP[index] == r.0 && newP[index + 1] == r.1; }
        SetU(newP[..index]) + r.0 + r.1 + SetU(newP[index + 2..]);
        { assert newP[..index] == elem[..index] ;}
        SetU(elem[..index]) + r.0 + r.1 + SetU(newP[index + 2..]);
        { assert newP[index + 2..] == elem[index + 1..] ;}
        SetU(elem[..index]) + r.0 + r.1 + SetU(elem[index + 1..]);
        { assert r.0 + r.1 == elem[index]; }
        SetU(elem[..index]) + elem[index] + SetU(elem[index + 1..]);
        { SplitUnion1(elem, index); }
        SetU(elem);
      }
      //    if one of r.0 or r.1 is empty remove it
      if r.0 == {} then RemoveEmpty(Partition(n, newP), index)
      else if r.1 == {} then RemoveEmpty(Partition(n, newP), index + 1)
      else Partition(n, newP)
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
      requires forall k:: 0 <= k < index ==> x !in elem[k]
      ensures c < |elem| && x in elem[c]
      ensures c < n
      decreases |elem| - index
    {
      // This lemma ensures we will find an index with x in elem[index]!
      ExistsIn(this, x);
      ValidMaxClasses(this);
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
      ensures Equiv(x, y) ==> exists k:: 0 <= k < |elem| && x in elem[k] && y in elem[k]
      ensures x == y ==> Equiv(x, y)
    {
      //    Prove that |p.elem|
      NotEmpty(this);
      assert GetClass(x) == GetClass(y) ==> x in elem[GetClass(x)] && y in elem[GetClass(y)];
      GetClass(x) == GetClass(y)
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
      forall x, x':: 0 <= x < x' < n ==> (Equiv(x, x') ==> p.Equiv(x, x'))
    }

  }

  function RemoveEmpty(p: Partition,  k: nat): (p': ValidPartition)
    requires 0 <= k < |p.elem|
    requires p.elem[k] == {}
    requires p.n > 0
    requires forall k, k':: 0 <= k < k' < |p.elem| ==> p.elem[k] * p.elem[k'] == {}
    requires SetU(p.elem) == set q {:nowarn} | 0 <= q < p.n
    requires forall i:: 0 <= i < |p.elem| && i != k ==> p.elem[i] != {}
    ensures p'.IsValid()
  {
    var p1 := Partition(p.n, p.elem[..k] + p.elem[k + 1..]);
    RemoveEmptySet(p, k);
    p1

  }

  function {:tailrecursion true} {:timeLimitMultiplier 8} SplitAllFrom(p: ValidPartition, f : nat --> nat --> bool, index: nat := 0, ghost from: nat := index): (p': ValidPartition)
      requires p.IsValid()
      requires from <= index <= |p.elem|
      requires forall x:nat :: index <= x < |p.elem| ==> f.requires(x)
      requires forall x :: index <= x < |p.elem| ==> (forall y:nat :: y < p.n ==> f(x).requires(y))
      requires forall x:nat :: index <= x < |p.elem| ==> (forall y:nat:: y in p.elem[x] ==> f(x).requires(y))
      decreases |p.elem| - index
      ensures p'.IsValid()
      ensures |p'.elem| >= |p.elem|
      ensures p'.elem[..from] == p.elem[..from]
      ensures p'.n == p.n
    {
      if |p.elem| == index then p 
      else
        var p1 := p.SplitAt(f(index), index);
        //  We may add one or zero sets depending on whether splitting elem[index]
        //  results in one empty set. If we get one set we advance to index + 1 and
        //  if we get two we advance to index + 2
        //  We have so shift f too
        var f': nat --> nat --> bool := (x:nat) requires index + 1 <= x < |p1.elem| => f(x - (|p1.elem| - |p.elem|));
        assert p1.elem[..from] == p.elem[..from];
        SplitAllFrom(p1, f', index + 1 + |p1.elem| - |p.elem|, from)
    }

  /**
    *   A valid partition cannot be empty.
    */
  lemma NotEmpty(p: Partition)
    requires p.IsValid()
    ensures |SetU(p.elem)| > 0
    ensures |p.elem| > 0
  {
    assert { 0 } <= SetU(p.elem);
  }

  /**   
    *   A partition p of {0, ..., n - 1} ensures that 
    *   0 <= k < n ==> k in a class of p.
    */
  lemma ExistsIn(p: Partition, k: nat)
    requires p.IsValid()
    requires 0 <= k < p.n
    ensures exists s:: 0 <= s < |p.elem| && k in p.elem[s]
  {
    if !exists s:: 0 <= s < |p.elem| && k in p.elem[s] {
      assert forall s:: 0 <= s < |p.elem| ==> k !in p.elem[s];
      assert false;
    }
  }

  /**
    *   If a seq has a unique empty set it can be removed. to make a Valid partition.
    */
  lemma RemoveEmptySet(p: Partition, k: nat)
    requires 0 <= k < |p.elem|
    requires p.elem[k] == {}
    requires p.n > 0
    requires forall k, k':: 0 <= k < k' < |p.elem| ==> p.elem[k] * p.elem[k'] == {}
    requires SetU(p.elem) == set q {:nowarn} | 0 <= q < p.n
    requires forall i:: 0 <= i < |p.elem| && i != k ==> p.elem[i] != {}

    ensures SetU(p.elem[..k] + p.elem[k + 1..]) == SetU(p.elem)
    ensures Partition(p.n, p.elem[..k] + p.elem[k + 1..]).IsValid()
  {
    var p1 := Partition(p.n, p.elem[..k] + p.elem[k + 1..]);
    NeutralEmptySet(p.elem, k);
  }

  /**
    *   The maximum number of classes in a partition of [0..n-1] is n.
    */
  lemma ValidMaxClasses(p: ValidPartition)
    ensures |p.elem| <= p.n
  {
    if |p.elem| > p.n {
      //  Just show that each set is included in {0, ..., n -1}
      forall k | 0 <= k < |p.elem|
        ensures p.elem[k] <= set x {:nowarn} | 0 <= x < p.n {
        SplitUnion1(p.elem, k);
        assert SetU(p.elem[..k]) + p.elem[k] + SetU(p.elem[k + 1..]) == SetU(p.elem);
        assert p.elem[k] <= SetU(p.elem);
      }
      //  Apply the shrinking lemma
      ShrinkingLemma(p.elem, p.n);
      assert |p.elem[|p.elem| - 1]| == 0;
    }
  }

  lemma {:axiom} AllClassesInSetU(p: ValidPartition)
    ensures forall k:: k in p.elem ==> k <= SetU(p.elem)
    ensures forall k:: 0 <= k < |p.elem| ==> p.elem[k] <= SetU(p.elem)


  //   lemma PartialFunShift(f: nat --> nat --> bool, f': nat --> nat --> bool, index: nat, p: ValidPartition)
  //     requires forall x:nat :: index <= x < |p.elem| ==> f.requires(x)
  //     requires forall x:nat :: index <= x < |p.elem| ==> (forall y:nat:: y in p.elem[x] ==> f(x).requires(y))
  //     requires f' == ((x:nat) requires index + 1 <= x < |p1.elem| => f(x - (|p1.elem| - |p.elem|)))
  //     ensures
  //       {

  //       }
  //    Some tests
  //   method {:test} Test1() {
  //     var p1 := Partition(4, [set q {:nowarn} | 0 <= q < 4]);
  //     PrintPartition(p1);
  //     var p2 := p1.SplitAllFrom((x => x % 2 == 0));
  //     PrintPartition(p2);
  //   }

  //   method {:test} Test2() {
  //     var p1 := Partition(20, [set q {:nowarn} | 0 <= q < 20]);
  //     PrintPartition(p1);
  //     var p2 := p1.SplitAllFrom((x => x % 2 == 0));
  //     var p3 := p2.SplitAllFrom((x => x / 3 == 0));
  //     var p4 := p3.SplitAllFrom((x => x / 4 == 0));
  //     PrintPartition(p4);
  //   }

  method {:tailrecursion true} PrintPartition(p: Partition)
  {
    for k := 0 to |p.elem| {
      var setToSeq := SetToSequence(p.elem[k]);
      print setToSeq, "\n";
    }
  }

  //    automaton
  //    0 - a -> 1 - b -> 2
  //    0 - b -> 3 - b -> 4
  //    predicate is:
  //    same enabled + s - x -> s'
  //    s ~ s' and     s - a -> s1 and s' - a -> s1' and s1 ~ s1'
  //    same class OK  GetClass(succ_a(s)) == GetClass(succ_a(s'));
  /*
  C0 = {0, 1, 3} C1 = {2, 4}
  get tgt class of 0 in {0, 1, 3}
  then sort according to who is equiv to 0 by succ_a(), succ_b 
  succ_a_b(0) = (GetClass(Some(x)), None)

  refine C0 = {0, 1, 3} with succ_a_b(s) == (GetClass(Some(x)), None)
  e.g. 
  succ_a_b(0) = (Some(1), Some(3)) -> class (Some(C0), Some(C0))

  succ_a_b(1) = (None, Some(C1)) != 
  succ_a_b(3) = (None, Some(C1)) != 

  C0 refined in { 0 }, {1, 3}
  Apply to {1, 3}
  succ_a_b(1) = (None, C1)
  succ_a_b(3) = (None, C1) done
  {0}, {1, 3}, {2, 4}
  */
  //   method {:test} Test3()
  //   {
  //     var p1 := Partition(5, [set q {:nowarn} | 0 <= q < 5]);
  //     // var p1 := Partition(5, [{0, 1, 3}, {2, 4}]);
  //     var m: map<(nat, nat), nat> :=
  //       map[
  //         (0, 0) := 1,
  //         (0, 1) := 3,
  //         (1, 1) := 2,
  //         (3, 1) := 4
  //       ];
  //     assert p1.IsValid();
  //     assert forall k:: k in m.Values  ==> 0 <= k < p1.n;
  //     PrintPartition(p1);
  //     var f: ValidPair -> (nat -> (nat -> bool)) :=
  //       (p: ValidPair) =>
  //         ((y: nat) => ((x: nat) => succ(x, p.1, p.0) == succ(y, p.1, p.0)));

  //     var pair1 := (p1, m);

  //     var p2 := p1.SplitAt(f(pair1)(0), 0);
  //     PrintPartition(p2);
  //     // PrintPartition(pair1.0);
  //     assert |p2.elem| > 1;
  //     var pair2 := (p2, m);
  //     var p3 := p2.SplitAt(f(pair2)(1), 1);
  //     PrintPartition(p3);

  //   }


  //   type ValidPair = x : (Partition, map<(nat, nat), nat>) | x.0.IsValid() && (forall k:: k in x.1.Values ==> k < x.0.n)
  //     witness (Partition(1, [{0}]), map[])

  //   function succ(x: nat, m: map<(nat, nat), nat>, p: ValidPartition): (Option<nat>, Option<nat>)
  //     requires forall k:: k in m.Values ==> 0 <= k < p.n
  //     requires p.IsValid()
  //   {
  //     NotEmpty(p);
  //     var s1 := if (x, 0) in m then
  //                 assert m[(x, 0)] in m.Values;
  //                 Some(p.GetClass(m[(x, 0)]))
  //               else None;
  //     var s2 := if (x, 1) in m then
  //                 assert m[(x, 1)] in m.Values;
  //                 Some(p.GetClass(m[(x, 1)]))
  //               else None;
  //     (s1, s2)
  //   }

  //   function foo(x: nat, p: Partition, m: map<(nat, nat), nat>): bool
  //   {

  //   }



  //   lemma foo707(p: Partition, p': Partition, x: nat, y: nat)
  //     requires p.IsValid()
  //     requires p'.IsValid()
  //     requires 0 <= x < p.n
  //     requires 0 <= y < p.n
  //     requires p.n == p'.n
  //     requires p.Equiv(x, y)
  //     requires p'.Equiv(x, y)


  //   lemma foo404(p: Partition, p': Partition)
  //     requires p.IsValid()
  //     requires p'.IsValid()
  //     requires p.n == p'.n
  //     requires p.Refines(p')
  //     // ensures forall k:: k in p.elem ==> exists k':: k' in p'.elem && k <= k'
  //   {
  //     NotEmpty(p);
  //     NotEmpty(p');
  //     assert |p'.elem| >= 1;

  //     forall k | 0 <= k < |p.elem|
  //       ensures exists k':: 0 <= k' < |p'.elem| && p.elem[k] <= p.elem[k'] {
  //       if p.elem[k] == {} {
  //         assert |p'.elem| >= 1;
  //         //   assume p.elem[k] <= p'.elem[0];
  //       } else {
  //         //   var x :| x in p.elem[k];
  //         //   assume x in p.elem[p.GetClass(x)];
  //         //   assume x < p.n;
  //         //   assume p.Equiv(x, x);

  //       }
  //       assume exists k':: 0 <= k' < |p'.elem| && p.elem[k] <= p.elem[k'];
  //     }

  //   }
  //   lemma GetClassUnique(p: Partition, x: nat)
  //     requires p.IsValid()
  //     requires 0 <= x < p.n
  //     ensures forall k:: 0 <= k < |p.elem| && k != p.GetClass(x) ==> x !in p.elem[k]
  //   {
  //     assume  forall k:: 0 <= k < |p.elem| && k != p.GetClass(x) ==> x !in p.elem[k];
  //   }

  //   lemma GetClassLemma(p: Partition, x: nat)
  //     requires p.IsValid()
  //     requires 0 <= x < p.n
  //     requires |p.elem| > 0
  //     ensures p.GetClass(x) < |p.elem|
  //     ensures x in p.elem[p.GetClass(x)]
  //   {
  //     // NotEmpty(p);
  //   }


}