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

  /**   For some reasons the following lemma cannot be proved. */
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

  function {:tailrecursion true} Zip<U, V>(u: seq<U>, v: seq<V>): seq<(U, V)>
    requires |u| == |v|
  {
    seq(|u|, i requires 0 <= i < |u| => (u[i], v[i]))
  }

  function {:tailrecursion true} UnZip<U, V>(x: seq<(U, V)>): (seq<U>, seq<V>)
    ensures |UnZip(x).0| == |UnZip(x).1| == |x|
    ensures forall k:: 0 <= k < |x| ==> (UnZip(x).0[k] == x[k].0 && UnZip(x).1[k] == x[k].1)
  {
    var x0 := seq(|x|, i requires 0 <= i < |x| => x[i].0);
    var x1 := seq(|x|, i requires 0 <= i < |x| => x[i].1);
    (x0 ,x1)
  }

  function {:tailrecursion true} Filter<U>(u: seq<U>, f: U -> bool): (r: seq<U>)
    ensures |r| <= |u|
    ensures forall x:: x in r ==> x in u
    ensures forall k:: 0 <= k < |r| ==> f(r[k])
    ensures forall x:: x in r ==> f(x)
  {
    if |u| == 0 then []
    else if f(u[0]) then [u[0]] + Filter(u[1..], f)
    else Filter(u[1..], f)
  }

  predicate {:tailrecursion true} Exists<T>(xs: seq<T>, f: T -> bool)
    ensures !Exists(xs, f) ==> forall k:: k in xs ==> !f(k)
    ensures !Exists(xs, f) ==> forall k:: 0 <= k < |xs| ==> !f(xs[k])
  {
    if |xs| == 0 then false
    else if f(xs[0]) then true
    else Exists(xs[1..], f)
  }

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
    *  Two distinc indices in the flat seq correspond to two 
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