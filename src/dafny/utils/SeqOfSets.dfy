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


include "MiscTypes.dfy"
/** 
  * Provides seqeuence of sets.
  */
module SeqOfSets {

  import opened MiscTypes

  /**
    *   Union of a seq of sets.
    */
  function {:tailrecursion true} SetU<T>(xs: seq<set<T>>): (r: set<T>)
    // ensures forall x:: x in r ==> exists k:: 0 <= k < |xs| && x in xs[k]
    ensures forall k:: 0 <= k < |xs| ==> xs[k] <= SetU(xs)
  {
    if |xs| == 0 then {}
    else xs[0] + SetU(xs[1..])
  }

  /**
    *   Intersection of a seq of sets.
    */
  function {:tailrecursion false} {:opaque} SetI<T>(xs: seq<set<T>>): (r: set<T>)
  {
    if |xs| == 0 then {}
    else if |xs| == 1 then xs[0]
    else xs[0] * SetI(xs[1..])
  }

  ghost predicate AllNonEmpty<T>(xs: seq<set<T>>)
  {
    forall k:: 0 <= k < |xs| ==> xs[k] != {}
  }

  lemma AllNonEmptySubset<T>(r1: seq<set<T>>, r2: seq<set<T>>)
    requires AllNonEmpty(r1)
    requires AllNonEmpty(r2)
    ensures AllNonEmpty(r1 + r2)
  {

  }

  ghost predicate DisjointAnyTwo<T>(xs: seq<set<T>>)
  {
    forall k, k':: 0 <= k < k' < |xs| ==> xs[k] * xs[k'] == {}
  }
 
  ghost predicate SetN(xs: seq<set<nat>>, n: nat)
  {
    // reveal_SetU();
    SetU(xs) == set z {:nowarn} | 0 <= z < n
  }

  lemma EmptySubsetIntersection<T>(a: set<T>, b: set<T>, c: set<T>, d: set<T>)
    requires a * b == {}
    requires c <= a && d <= b
    ensures c * d == {}
  {
  }

  /**
    *   Every value in a class is less than n.
    *   Every 0 <= k < n is is in SetU(xs)
    */
  lemma AllBoundedBy(xs: seq<set<nat>>, n: nat)
    requires SetN(xs, n)
    ensures forall k, e:: k in xs && e in k ==> 0 <= e < n
    ensures forall k, e:: 0 <= k < |xs| &&  e in xs[k] ==> 0 <= e < n
    ensures forall e:: 0 <= e < n <==> e in SetU(xs)
  { //  Thanks Dafny
  }

  /**
    *   If xs is {0, ..., n - 1} then 
    *   every 0 <= k < n is in one of the classes of xs.
    */
  lemma LessThanNIsInAClass(xs: seq<set<nat>>, n: nat, k: nat)
    requires SetN(xs, n)
    requires 0 <= k < n
    ensures exists i:: 0 <= i < |xs| && k in xs[i]
  {
    if !(exists i:: 0 <= i < |xs| && k in xs[i]) {
      SubLessThan(xs, k);
    }
  }

  /**
    *   For each t in SetU(xs), there is a class
    *   containing t.
    */
  lemma SubLessThan<T>(xt: seq<set<T>>, t: T)
    requires t in SetU(xt)
    ensures exists k:: 0 <= k < |xt| && t in xt[k]
  { //  Thanks Dafny
    // reveal_SetU();
  }

  /**   
    *   If any two disjoint then the head set 
    *   does not intersection the union of the tail.
    */
  lemma DisjointFirst<T>(xs: seq<set<T>>)
    requires DisjointAnyTwo(xs)
    requires |xs| >= 1
    ensures xs[0] * SetU(xs[1..]) == {}
  {
    if  xs[0] * SetU(xs[1..]) != {} {
      var e :| e in xs[0] && e in SetU(xs[1..]);
      SubLessThan(xs[1..], e);
      var k :| 0 <= k < |xs[1..]| && e in (xs[1..])[k];
      assert e in xs[k + 1];
      assert e in xs[0] * xs[k + 1];
      assert !DisjointAnyTwo(xs);
      assert false;
    }
  }

  /**
    *   The maximum number of classes in a partition of
    *   {0, ..., n - 1} is n.
    */
  lemma MaxNumberOfClasses(xs: seq<set<nat>>, n: nat)
    requires SetN(xs, n)
    requires DisjointAnyTwo(xs)
    requires AllNonEmpty(xs)
    ensures |xs| <= n
  {
    if |xs| > n {
      SizeOfNatsUpToNBound(n, SetU(xs));
      MinNumberOfClasses(xs);
      assert |SetU(xs)| >= |xs|;
    }
  }

  /**
    *   If disjoint two by two and non empty, then 
    *   the partition has more |xs| element.
    *   @note   Used to prove that the number of 
    *           classes for {0, ..., n - 1} is bounded 
    *           by n.
    */
  lemma MinNumberOfClasses<T>(xs: seq<set<T>>)
    requires DisjointAnyTwo(xs)
    requires AllNonEmpty(xs)
    ensures |SetU(xs)| >= |xs|
  {
    // reveal_SetU();
    if |xs| == 0 {
      //  
    } else {
      calc == {
        |SetU(xs)|;
        |xs[0] + SetU(xs[1..])|;
         { DisjointFirst(xs); }
        |xs[0]| + |SetU(xs[1..])|;
      >= { MinNumberOfClasses(xs[1..]); }
        |xs[0]| + |xs[1..]|;
      }
    }
  }

  /**
    *   Split a set into two subsets X and Y such that X = f^-1(true) and Y = f^-1(false)
    */
  function {:opaque} SplitSet(xs: set<nat>, f: nat --> bool): (r: (set<nat>, set<nat>))
    requires forall x:: x in xs ==> f.requires(x)
    ensures xs == r.0 + r.1
    ensures r.0 * r.1 == {}
    ensures forall x:: x in r.0 ==> f(x)
    ensures forall x:: x in r.1 ==> !f(x)
  {
    var asSeq := SetToSequence(xs);
    SplitSeqTail(asSeq, f)
  }

  /**
    *   Split a sequence of sets into two subsets X and Y such that X = f^-1(true) and Y = f^-1(false)
    */
  function {:tailrecursion true} {:opaque} SplitSeqOfSet(xs: seq<set<nat>>, f: nat -> bool): (r: seq<(set<nat>, set<nat>)>)
    ensures |xs| == |r|
    ensures forall k:: 0 <= k < |r| ==> r[k].0 * r[k].1 == {}
    ensures forall k:: 0 <= k < |r| ==> r[k].0 + r[k].1 == xs[k]
  {
    if |xs| == 0 then []
    else
      [SplitSet(xs[0], f)] + SplitSeqOfSet(xs[1..], f)
  }

  //  Helpers

  /**
    *   Iterate over sets. 
    *   @link{https://leino.science/papers/krml275.html}
    */
  function {:tailrecursion true} {:opaquex} SetToSequence(s: set<nat>): (r: seq<nat>)
    ensures |s| == |r| 
    ensures forall i :: i in s <==> i in r
  {
    if s == {} then []
    else
      ThereIsAMinimum(s);
      var x :| x in s && forall y :: y in s ==> x <= y;
      [x] + SetToSequence(s - {x})
  }

  //    Helper Lemmas

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

  /**
    *   Distributivity of U over +.
    */
  lemma DistribUnion<T>(a : seq<set<T>>, b: seq<set<T>>)
    ensures SetU(a + b) == SetU(a) + SetU(b)
  {
    // reveal_SetU();
    if |a| == 0 {
      assert [] + b == b;
      assert SetU(a) == {};
    } else {
      calc == {
        SetU(a + b);
        { assert a == [a[0]] + a[1..]; }
        SetU([a[0]] + a[1..] + b);
        { assert ([a[0]] + a[1..] + b)[1..] == a[1..] + b ; }
        a[0] + SetU(a[1..] + b);
        //  induction
      }
    }
  }

  lemma DistribUnion3<T>(a : seq<set<T>>, b: seq<set<T>>, c: seq<set<T>>)
    ensures SetU(a + b + c) == SetU(a) + SetU(b) + SetU(c)
  {
    DistribUnion(a + b, c);
    DistribUnion(a, b);
  }

  /**
    *   Split a sequence around an index.
    */
  lemma SplitUnion1<T>(xs: seq<set<T>>, index: nat)
    requires index < |xs|
    ensures SetU(xs[..index]) + xs[index] + SetU(xs[index + 1..]) == SetU(xs)
  {
    // reveal_SetU();
    calc == {
      SetU(xs);
      { assert xs == xs[..index] + [xs[index]] + xs[index + 1..] ; }
      SetU(xs[..index] + [xs[index]] + xs[index + 1..]);
      { DistribUnion(xs[..index] + [xs[index]], xs[index + 1..]) ; }
      SetU(xs[..index] + [xs[index]]) + SetU(xs[index + 1..]);
      { DistribUnion(xs[..index], [xs[index]]) ; }
      SetU(xs[..index]) + SetU([xs[index]]) + SetU(xs[index + 1..]);
      SetU(xs[..index]) + xs[index] + SetU(xs[index + 1..]);
    }
  }

  /**
    *   The size of set that has only nat < n is bounded by n.
    */
  lemma SizeOfNatsUpToNBound(n: nat, Y: set<nat>)
    requires Y == set x {:nowarn} | 0 <= x < n
    ensures |Y| == n
  {
    if n == 0 || Y == {} {
      //  Thanks Dafny
    } else if n - 1 in Y {
      var X := Y - { n - 1};
      assert X + {n -1} == Y;
      assert |Y| == |X + {n -1}| <= |X| + |{n - 1}|;
      assert |Y| <= |X| + 1;
      SizeOfNatsUpToNBound(n - 1, X);
    } else {
      assert n - 1 !in Y;
      assert Y == set x {:nowarn} | 0 <= x < n - 1;
      SizeOfNatsUpToNBound(n - 1, Y);
    }
  }

  /**
    *   Size of union of disjoint sets is the sum of the sizes of
    *   the sets.
    */
  lemma SizeOfUnion<T>(a: set<T>, b: set<T>)
    requires a * b == {}
    ensures |a + b| == |a| + |b|
  { //  Thanks Dafny
  }

  /**
    *   Split a sequence of nat according to a function value f.
    *   Tail recursivse version.
    */
  function {:tailrecursion true} {:opaque} SplitSeqTail(xs: seq<nat>, f: nat --> bool, cTrue: set<nat> := {}, cFalse: set<nat> := {}, index: nat := 0): (r: (set<nat>, set<nat>))
    requires index <= |xs|
    requires forall  k:: k in xs ==> f.requires(k)
    requires  forall k:: k in xs[..index] <==> k in cTrue + cFalse
    requires cTrue * cFalse == {}
    requires forall k:: k in cTrue ==> f(k)
    requires forall k:: k in cFalse ==> !f(k)
    ensures  forall k:: k in xs <==> k in r.0 + r.1
    ensures r.0 * r.1 == {}
    ensures forall k:: k in r.0 ==> f(k)
    ensures forall k:: k in r.1 ==> !f(k)

    decreases |xs| - index
  {
    if |xs| == index then (cTrue, cFalse)
    else if f(xs[index]) then
      assert xs[..index + 1] == xs[..index] + [xs[index]];
      SplitSeqTail(xs, f, cTrue + {xs[index]}, cFalse, index + 1)
    else
      assert xs[..index + 1] == xs[..index] + [xs[index]];
      SplitSeqTail(xs, f, cTrue, cFalse + {xs[index]}, index + 1)
  }

  /**
    *   Split a sequence of nat according to a function value f.
    *   Simple non tail-rec version.
    */
  ghost function {:tailrecursion false} SplitSeq(xs: seq<nat>, f: nat -> bool): (r: (set<nat>, set<nat>))
    ensures forall k:: k in r.0 ==> f(k)
    ensures forall k:: k in r.1 ==> !f(k)
    ensures r.0 * r.1 == {}
    ensures forall k:: k in xs && f(k) <==> k in r.0
    ensures forall k:: k in xs && !f(k) <==> k in r.1
    ensures forall k:: k in xs <==> k in r.0 + r.1
  {
    if |xs| == 0 then ({}, {})
    else
      var r := SplitSeq(xs[1..], f);
      if f(xs[0]) then (r.0 + {xs[0]}, r.1)
      else
        (r.0, r.1 + {xs[0]})
  }

  /**
    *   Flattening a seq of disjoint sets yield 
    *   a set of disjoint sets.
    */
  lemma NonFlatDisjointImpliesFlatDisjoint(r: seq<seq<set<nat>>>, r': seq<set<nat>>)
    requires r' == Flatten(r)
    requires forall i, i':: 0 <= i < i' < |r| ==> SetU(r[i]) * SetU(r[i']) == {}
    requires forall i:: 0 <= i < |r| ==> DisjointAnyTwo(r[i])
    ensures DisjointAnyTwo(Flatten(r))
  {
    forall i, i' | 0 <= i < i' < |r'|
      ensures r'[i] * r'[i'] == {}
    {
      var (i1, k1) := UnFlatIndex(r, r', i);
      var (i2, k2) := UnFlatIndex(r, r', i');
      FlatDistinctImpliesUnFlatDistinct(r, r', i, i');
    }
  }

  /**
    *   Flatten preserves SetU.
    */
  lemma FlattenPreservesSetU(xs: seq<set<nat>>, r: seq<seq<set<nat>>>)
    requires |xs| == |r|
    requires forall i:: 0 <= i < |r| ==> SetU(r[i]) == xs[i]
    ensures SetU(Flatten(r)) == SetU(xs)
  {
    // reveal_SetU();
    if |xs| == 0 {
      //  Thanks Dafny
    } else {
      calc == {
        SetU(Flatten(r));
        SetU(r[0] + Flatten(r[1..]));
        { DistribUnion(r[0], Flatten(r[1..])); }
        SetU(r[0]) + SetU(Flatten(r[1..]));
        xs[0] + SetU(Flatten(r[1..]));
        { FlattenPreservesSetU(xs[1..], r[1..]); }
        xs[0] + SetU(xs[1..]);
      }
    }
  }

  /**
    *   Flattening all non-empty sets preserves all non-empty.
    */
  lemma FlattenAllNonEmpty(r: seq<seq<set<nat>>>, n: nat)
    requires forall i:: 0 <= i < |r| ==> AllNonEmpty(r[i])
    requires forall i, k:: 0 <= i < |r| && 0 <= k < |r[i]| ==> forall x:: x in r[i][k] ==> x < n
    ensures forall i:: i in Flatten(r) ==> i != {}
    ensures AllNonEmpty(Flatten(r))
    ensures forall i:: i in Flatten(r) ==> forall x:: x in i ==> x < n
  { // Thanks Dafny
  }

}