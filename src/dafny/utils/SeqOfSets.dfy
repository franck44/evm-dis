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

/** 
  * Provides seqeuence of sets.
  */
module SeqOfSets {

  /**
    *   Union of a seq of sets.
    */
  function {:tailrecursion true} SetU<T>(xs: seq<set<T>>): (r: set<T>)
    ensures forall x:: x in r ==> exists k:: 0 <= k < |xs| && x in xs[k]
  {
    if |xs| == 0 then {}
    else xs[0] + SetU(xs[1..])
  }

  /**
    *   Intersection of a seq of sets.
    */
  function {:tailrecursion false} SetI<T>(xs: seq<set<T>>): (r: set<T>)
  {
    if |xs| == 0 then {}
    else if |xs| == 1 then xs[0]
    else xs[0] * SetI(xs[1..])
  }

  /**
    *   Split a set into two subsets X and Y such that X = f^-1(true) and Y = f^-1(false)
    */
  function SplitSet(xs: set<nat>, f: nat -> bool): (r: (set<nat>, set<nat>))
    ensures xs == r.0 + r.1
    ensures r.0 * r.1 == {}
  {
    var asSeq := SetToSequence(xs);
    SplitSeqTail(asSeq, f)
  }

  /**
    *   Split a sequence of sets into two subsets X and Y such that X = f^-1(true) and Y = f^-1(false)
    */
  function {:tailrecursion true} SplitSeqOfSet(xs: seq<set<nat>>, f: nat -> bool): (r: seq<(set<nat>, set<nat>)>)
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
  function {:tailrecursion true} SetToSequence(s: set<nat>): (r: seq<nat>)
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

  /**
    *   Split a sequence around an index.
    */
  lemma SplitUnion1<T>(xs: seq<set<T>>, index: nat)
    requires index < |xs|
    ensures SetU(xs[..index]) + xs[index] + SetU(xs[index + 1..]) == SetU(xs)
  {
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
    *   Split a sequence arount two consecutive indices.
    */
  lemma SplitUnion2<T>(xs: seq<set<T>>, index: nat)
    requires index < |xs| - 1
    ensures SetU(xs[..index]) + xs[index] + xs[index + 1] + SetU(xs[index + 2..]) == SetU(xs)
  {
    calc == {
      SetU(xs);
      { assert xs == xs[..index] + [xs[index]] + xs[index + 1..]; }
      SetU(xs[..index] + [xs[index]] + xs[index + 1..]);
      { SplitUnion1(xs, index); }
      SetU(xs[..index]) + xs[index] + SetU(xs[index + 1..]);
      SetU(xs[..index]) + xs[index] + SetU([xs[index + 1..][0]] + xs[index + 1..][1..]);
      { SplitUnion1(xs[index + 1..], 0); }
      SetU(xs[..index]) + xs[index] + xs[index + 1..][0] + SetU(xs[index + 1..][1..]);
      { assert xs[index + 1..][1..] == xs[index + 2..]; }
      SetU(xs[..index]) + xs[index] + xs[index + 1] + SetU(xs[index + 2..]);
    }
  }

  /**
    *   An empty set in xs does not contribute to SetU(xs).
    */
  lemma NeutralEmptySet<T>(xs: seq<set<T>>, k: nat)
    requires 0 <= k < |xs|
    requires xs[k] == {}
    ensures SetU(xs) == SetU(xs[..k] + xs[k + 1..])
  {
    SplitUnion1(xs, k);
    calc == {
      SetU(xs);
      { SplitUnion1(xs, k); }
      SetU(xs[..k]) + xs[k] + SetU(xs[k + 1..]);
      calc == {
        SetU(xs[..k]) + xs[k];
        SetU(xs[..k]) + {};
        SetU(xs[..k]);
      }
      SetU(xs[..k]) + SetU(xs[k + 1..]);
      { DistribUnion(xs[..k], xs[k + 1..]);}
      SetU(xs[..k] + xs[k + 1..]);
    }
  }

  /**
    *   For a seq of disjoint and non empty sets, within a finite set {0, ..., n -1 }
    *   the last set cannot contain elements from the previous sets.
    *   Hence its size decreases.
    */
  lemma ShrinkingLemma(xs: seq<set<nat>>, n: nat)
    requires forall k:: 0 <= k < |xs| ==> {} < xs[k] <= set x {:nowarn} | 0 <= x < n
    requires forall k, k':: 0<= k < k' < |xs| ==> xs[k] * xs[k'] == {}
    requires |xs| > 0
    ensures |xs[|xs| - 1]| <= n - |SetU(xs[..|xs| - 1])|
    ensures |xs| > n ==> |xs[|xs| - 1]| == 0
  {
    calc == {
      n;
    >= {SizeOfNatsUpToNBound(n, SetU(xs));}
      |SetU(xs)|;
       { SplitUnion1(xs, |xs| - 1); }
      |SetU(xs[..|xs| - 1]) + xs[|xs| - 1]|;
    }
    if |xs| > n {
      calc <= {
        |xs[|xs| - 1]|;
        n - |SetU(xs[..|xs| - 1])|;
        { MinSizeOfNonEmptyDisjoint(xs[..|xs| - 1]); }
        0;
      }
    }
  }

  /**
    *   For a seq of non empty and disjoint sets of size k, SetU has more then k elements.
    */
  lemma MinSizeOfNonEmptyDisjoint(xs: seq<set<nat>>)
    requires forall k:: 0 <= k < |xs| ==> {} < xs[k]
    requires forall k, k':: 0<= k < k' < |xs| ==> xs[k] * xs[k'] == {}
    ensures |SetU(xs)| >= |xs|
  {
    if |xs| == 0 {
      //  Thanks Dafny
    } else {
      SplitUnion1(xs, |xs| - 1);
      assert SetU(xs[..|xs| - 1]) + xs[|xs| - 1] == SetU(xs);
      //   foo302(xs, |xs| - 1);
      assert xs[|xs| - 1] * SetU(xs[..|xs| - 1]) == {};
      assert |xs[|xs| - 1]| >= 1;
      SizeOfUnion(xs[|xs| - 1], SetU(xs[..|xs| - 1]));
      assert |SetU(xs)| == |SetU(xs[..|xs| - 1])| + |xs[|xs| - 1]| ;
      assert |SetU(xs)| >= |SetU(xs[..|xs| - 1])| + 1 ;
      MinSizeOfNonEmptyDisjoint(xs[..|xs| - 1]);
    }
  }

  /**
    *   The size of set that has only nat < n is bounded by n.
    */
  lemma SizeOfNatsUpToNBound(n: nat, Y: set<nat>)
    requires Y <= set x {:nowarn} | 0 <= x < n
    ensures |Y| <= n
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
      assert Y <= set x {:nowarn} | 0 <= x < n - 1;
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

  /**
    *   Split a sequence of nat according to a function value f.
    *   Tail recursice version.
    */
  function {:tailrecursion true} SplitSeqTail(xs: seq<nat>, f: nat -> bool, cTrue: set<nat> := {}, cFalse: set<nat> := {}, index: nat := 0): (r: (set<nat>, set<nat>))
    requires index <= |xs|
    requires  forall k:: k in xs[..index] <==> k in cTrue + cFalse
    requires cTrue * cFalse == {}
    requires forall k:: k in cTrue ==> f(k)
    requires forall k:: k in cFalse ==> !f(k)
    ensures  forall k:: k in xs <==> k in r.0 + r.1
    ensures r.0 * r.1 == {}
    ensures forall k:: k in cTrue ==> f(k)
    ensures forall k:: k in cFalse ==> !f(k)

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

}