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
  * Provides Option type.
  */
module MiscTypes {

  datatype Try<T> = Success(v: T) | Failure(msg: string)

  datatype Option<T> = None | Some(v: T)
  {
    function Extract(): T
      requires this.Some?
    {
      this.v
    }
  }

  datatype Either<T, U> = Left(l: T) | Right(r: U)
  {
    function Left(): T
      requires this.Left?
    {
      this.l
    }

    function Right(): U
      requires this.Right?
    {
      this.r
    }
  }

  /** Attempt at defining a constraint on functions  */
  type WellDefined<!K(!new)> =
    f: (K, seq<K>) -> Option<K> | (forall x: K, xs: seq<K> {:triggers f(x, xs)} :: f(x, xs).Some? ==> f(x, xs).v in xs)
    witness ( (x: K, xs: seq<K>) => None)


  type WellDefined2<!K(!new)> =
    f: (K, seq<K>) -> Option<nat> | (forall x: K, xs: seq<K> {:triggers f(x, xs)} :: f(x, xs).Some? ==> f(x, xs).v < |xs|)
    witness ( (x: K, xs: seq<K>) => None)

  type Foo = f: nat -> nat |  (forall x: nat :: x < 2 ==> f(x) == 0)
    witness ((x: nat) => 0)

  predicate Foobar(f: Foo)
  {
    foo101(f);
    assert forall x: nat :: x < 2 ==> f(x) == 0;
    true
  }

  lemma {:axiom} foo101(f: Foo)
    ensures forall x: nat :: x < 2 ==> f(x) == 0

  /**   For some reasons the following lemmas cannot be proved by Dafny. */
  lemma {:axiom} Foo101<K(!new)>(f: WellDefined<K>)
    ensures forall x: K, xs: seq<K> :: f(x, xs).Some? ==> f(x, xs).v in xs
  //   {
  //     assume forall x: K, xs: seq<K> :: f(x, xs).Some? ==> f(x, xs).v in xs;
  //   }

  lemma {:axiom} Foo102<K(!new)>(f: WellDefined2<K>)
    ensures forall x: K, xs: seq<K> :: f(x, xs).Some? ==> f(x, xs).v < |xs|
  // {}
  //   {
  //     assume forall x: K, xs: seq<K> :: f(x, xs).Some? ==> f(x, xs).v in xs;
  //   }


  //    Helper functions for sequences

  /**   Last element */
  function Last<T>(x: seq<T>): T
    requires |x| > 0
  {
    x[|x| - 1]
  }

  /**
    *  Drop the first n elements of a seq.
    */
  function Drop<T>(x: seq<T>, n: nat): seq<T>
    requires n <= |x|
    ensures |Drop(x, n)| == |x| - n
  {
    x[n..]
  }

  /**
    * Initial segment (all but the last element).
    */
  function Init<T>(x: seq<T>): seq<T>
    requires 1 <= |x|
    ensures |Init(x)| == |x| - 1
  {
    x[..|x| - 1]
  }

  /**
    *  Zip two seqs into a seq of pairs.
    */
  function {:tailrecursion true} Zip<U, V>(u: seq<U>, v: seq<V>): seq<(U, V)>
    requires |u| == |v|
  {
    seq(|u|, i requires 0 <= i < |u| => (u[i], v[i]))
  }

  /**
    *  Unzip a seq of pairs into two seqs.
    */
  function {:tailrecursion true} UnZip<U, V>(x: seq<(U, V)>): (seq<U>, seq<V>)
    ensures |UnZip(x).0| == |UnZip(x).1| == |x|
    ensures forall k:: 0 <= k < |x| ==> (UnZip(x).0[k] == x[k].0 && UnZip(x).1[k] == x[k].1)
  {
    var x0 := seq(|x|, i requires 0 <= i < |x| => x[i].0);
    var x1 := seq(|x|, i requires 0 <= i < |x| => x[i].1);
    (x0 ,x1)
  }

  /**
    *   Filter a seq according to a predicate.
    */
  function {:tailrecursion true} Filter<U>(u: seq<U>, f: U --> bool): (r: seq<U>)
    ensures |r| <= |u|
    requires forall x:: x in u ==> f.requires(x)
    ensures forall x:: x in r ==> x in u
    ensures forall k:: 0 <= k < |r| ==> f(r[k])
    ensures forall x:: x in r ==> f(x)
  {
    if |u| == 0 then []
    else if f(u[0]) then [u[0]] + Filter(u[1..], f)
    else Filter(u[1..], f)
  }

  /**
    *   Determine if an element that satisfies a predicate is in a seq.
    */
  predicate {:tailrecursion true} Exists<T>(xs: seq<T>, f: T -> bool)
    ensures !Exists(xs, f) ==> forall k:: k in xs ==> !f(k)
    ensures !Exists(xs, f) ==> forall k:: 0 <= k < |xs| ==> !f(xs[k])
  {
    if |xs| == 0 then false
    else if f(xs[0]) then true
    else Exists(xs[1..], f)
  }

  /**
    * Flatten a seq of seq into a seq.
    */
  function Flatten<T>(x: seq<seq<T>>): seq<T>
  {
    if |x| == 0 then []
    else x[0] + Flatten(x[1..])
  }

  /**   Map each value of a seq according to a function. */
  function Map<T, U>(t: seq<T>, f: T -> U): seq<U>
    ensures |t| == |Map(t, f)|
    ensures forall i:: 0 <= i < |t| ==> Map(t, f)[i] == f(t[i])
  {
    seq(|t|, i requires 0 <= i < |t| => f(t[i]))
  }

  /**
    *  Map each value of a seq according to a _Partial_ function.
    */
  function MapP<T, U>(t: seq<T>, f: T --> U): seq<U>
    requires forall i:: 0 <= i < |t| ==> f.requires(t[i])
    ensures |t| == |MapP(t, f)|
    ensures forall i:: 0 <= i < |t| ==> MapP(t, f)[i] == f(t[i])
  {
    seq(|t|, i requires 0 <= i < |t| => f(t[i]))
  }

  /**
    *  Fold left a function.
    */
  function FoldLeft<T, U>(t: seq<T>, u0: U, f: (U, T) -> U): U
  {
    if |t| == 0 then u0
    else FoldLeft(t[1..], f(u0, t[0]), f)
  }

  /** Find the index of an element in a list.  
    * @param x  The list.
    * @param t  The element to find.
    * @return   The index of the element in the list, 
    *           or None if the element is not in the list.
    */
  function {:opaque} Find<T(==)>(x: seq<T>, t: T): Option<nat>
    ensures Find(x, t).Some? <==> t in x
    ensures Find(x, t).Some? ==> Find(x, t).Extract() < |x|
    ensures Find(x, t).Some? ==> x[Find(x, t).Extract()] == t
    ensures Find(x, t).None? <==> t !in x
  {
    FindRec(x, t)
  }

  /**
    *  Find the index of an element in a list or None if the element is not in the list.
    */
  function {:tailrecursion true} {:opaque} FindRec<T(==)>(x: seq<T>, t: T, i: nat := 0, ghost c: seq<T> := x): Option<nat>
    requires |c| == i + |x|
    requires c[i..] == x
    ensures FindRec(x, t, i, c).Some? ==> t in c
    ensures FindRec(x, t, i, c).Some? ==> FindRec(x, t, i, c).Extract() < |c|
    ensures FindRec(x, t, i, c).Some? ==> c[FindRec(x, t, i, c).Extract()] == t
    ensures FindRec(x, t, i, c).None? <==> t !in x
    decreases |x|
  {
    if |x| == 0 then None
    else if x[0] == t then Some(i)
    else FindRec(x[1..], t, i + 1, c)
  }

  //    Helper Lemmas

  /**   
    *  Given an index in a flat seq, retrieve the pair of indices
    *   that would have been used to access the element in the
    *   original seq of seq.
    */
  ghost function UnFlatIndex<T>(r: seq<seq<set<T>>>, r': seq<set<T>>, j: nat): (n: (nat, nat))
    requires r' == Flatten(r)
    requires j < |r'|
    ensures 0 <= n.0 < |r|
    ensures 0 <= n.1 < |r[n.0]|
    ensures r'[j] == r[n.0][n.1]
  {
    if |r| == 0 then (0, 0)
    else if j < |r[0]| then (0, j)
    else
      var i := UnFlatIndex(r[1..], r'[|r[0]|..], j - |r[0]|);
      (i.0 + 1, i.1)
  }

  /**
    *    Add a key value pair top a map of seq.
    */
  function AddKeyVal<T(==)>(m: map<T, seq<T>>, key: T, val: T): (m': map<T, seq<T>>)
    requires key in m
    ensures m'.Keys == m.Keys
    ensures forall k:: k in m && k != key ==> m[k] == m'[k]
    ensures m'[key] == m[key] + [val]
  {
    m[key := m[key] + [val]]
  }

  /**
    * If a seq satisfies a property, and a new element that satisfies the 
    * the property is added at the end of the seq, then the property is satisfied by the 
    * new seq.
    */
  lemma ExtendByOneGoodIsGood<T>(index: nat, js: seq<T>, p: T -> bool)
    requires index < |js|
    requires  forall j:: 0 <= j < index  ==> p(js[j])
    requires p(js[index])
    ensures forall j:: 0 <= j < index + 1 ==> p(js[j])
  { //    Thanks Dafny
  }

  /**
    * If two maps are revsered maps, then adding (key, val) to m and and (val, key) to m'
    * preserves the reverse map property.
    */
  lemma ReverseAddKeyValPreservesReverseMaps<T>(m: map<T, seq<T>>, m': map<T, seq<T>>, i: T, j: T)
    requires i in m
    requires j in m'
    requires IsReverseMap(m, m')
    ensures IsReverseMap(AddKeyVal(m, i, j), AddKeyVal(m', j, i))
  {   //  Thanks Dafny
  }

  lemma ReverseMapsIsCongruent<T>(m1: map<T, seq<T>>, m1': map<T, seq<T>>, m2: map<T, seq<T>>, m2': map<T, seq<T>>)
    requires m1 == m2
    requires m1' == m2'
    requires IsReverseMap(m1, m1')
    ensures IsReverseMap(m2, m2')
  {   //  Thanks Dafny
  }


  /**
    * Whether a map is the reverse of another map.
    */
  ghost predicate IsReverseMap<T(!new)>(m: map<T, seq<T>>, m': map<T, seq<T>>)
  {
    forall src, tgt::
      src in m && tgt in m[src] <==> tgt in m' && src in m'[tgt]
  }

  /**
    *  Two distinct indices in the flat seq correspond to two 
    *   distinct pair of indices in the original seq of seq.
    */
  lemma FlatDistinctImpliesUnFlatDistinct(r: seq<seq<set<nat>>>, r': seq<set<nat>>, j: nat, j': nat)
    requires r' == Flatten(r)
    requires 0 <= j < j' < |r'|
    ensures UnFlatIndex(r, r', j) != UnFlatIndex(r, r', j')
  {
    if |r| == 0 {
      //  Thanks Dafny
    } else if j < |r[0]| && j' < |r[0]| {
      assert UnFlatIndex(r, r', j) == (0, j);
      assert UnFlatIndex(r, r', j') == (0, j');
      assert j != j';
    } else if j < |r[0]| && j' >= |r[0]| {
      assert UnFlatIndex(r, r', j) == (0, j);
      assert UnFlatIndex(r, r', j').0 >= 1;
    } else if j >= |r[0]| && j' < |r[0]| {
      assert UnFlatIndex(r, r', j) == (1, j - |r[0]|);
      assert UnFlatIndex(r, r', j') == (0, j');
      assert j != j';
    } else {
      FlatDistinctImpliesUnFlatDistinct(r[1..], r'[|r[0]|..], j - |r[0]|, j' - |r[0]|);
    }
  }

  /**
    *    If all the non flat seqs are non-emtpy, then the
    *    flat seq has at least the same number of elements.
    */
  lemma MinSizeOfFlattenForAllNonEmpty(r: seq<seq<set<nat>>>)
    requires forall i:: 0 <= i < |r| ==> |r[i]| >= 1
    ensures |Flatten(r)| >= |r|
  {
    //  Thanks Dafny
  }

}