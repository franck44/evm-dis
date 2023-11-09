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
module Automata {

  import opened MiscTypes
  import Int

  datatype Node<T> =
      Num(index: nat, prop: T)
    | Sink()

  datatype Edge<U> = Edge(src: nat, lab: U, tgt: nat)

  /** Deterministic transition relation. 
    *
    *   0 is the starting state. A sink state is a state that is not
    *   in the map.   
    */
  type Transitions = map<(nat, bool), nat>

  type Transitions2<T(==)> = map<(T, bool), T>


  //   predicate IsDeterministic(tr: Transitions)
  //   {
  //     forall k, k':: k in tr.Keys && k' in tr.Keys  ==>
  //                      k.0 == k'.0 ==> k.1 != k'.1
  //   }

  datatype Auto = Auto(numStates: nat, tr: Transitions, final: nat := 0)

  datatype Auto2<T> = Auto2(init: T, tr: Transitions2<T>, refSet: set<T>, bound: nat)


  
  type ValidAuto2 = a: Auto2<nat> | IsBounded(a.refSet, a.bound) witness Auto2(0, map[], {}, 0)

  type ValidAuto = a: Auto |
      && forall k:: k in a.tr.Keys ==> k.0 < a.numStates
                                       && forall k:: k in a.tr.Values ==> k < a.numStates
    witness Auto(0, map[], 0)

  //   function Union<T>(tr1: Transitions, tr2: Transitions, s1: nat, s2: nat, lastState: nat, computedStates: map<(Option<nat>, Option<nat>), nat>): map<(Option<nat>, Option<nat>), nat>
  //   {
  //     //  get successors of s1 and s2 on false
  //     match SuccProd(s1, s2, false)
  //         case (None, None) => computedStates
  //         case (Some(k), None) => Union(tr1, [], k, )
  //         case (None, Some(k)) =>
  //         case (Some(k), Some(k')) =>
  //     // var succ1, succ2 := Succ(s1, tr1), Succ(s2, tr2);
  //     //  False successors
  //     // match (succ1.0, succ2.0)
  //     //     case (None, None) => computed
  //     //     case (Some(k), None) => computed + Unfold()
  //     //     case (None, Some(k)) => tr1
  //     //     case (Some(k), Some(k')) => tr1
  //     //     case  => tr1
  //     // tr1
  //   }

  function Succ(s: nat, tr: Transitions, exit: bool): Option<nat>
  {
    if (s, exit) in tr then Some(tr[(s, exit)])
    else None
  }

  function UnionSucc(a1: ValidAuto, a2: ValidAuto, s1: Option<nat>, s2: Option<nat>, exit: bool): (r: (Option<nat>, Option<nat>))
    ensures r.0.Some? ==> r.0.v < a1.numStates
    ensures r.1.Some? ==> r.1.v < a2.numStates
  {
    var s1' := if s1.None? || ((s1.v, exit) !in a1.tr) then None else Some(a1.tr[(s1.v, exit)]);
    var s2' := if s2.None? || ((s2.v, exit) !in a2.tr) then None else Some(a2.tr[(s2.v, exit)]);
    (s1', s2')
  }

  method DFS(a1: ValidAuto, s1: nat := 0, seen: set<nat> := {}, maxIter: nat)
    decreases maxIter
  {
    match Succ(s1, a1.tr, false) {
      case None =>  //    Explore true branch

      case Some(v) =>
        if v !in seen && maxIter > 0 {
          print "s", s1, " -- false -> ", "s", v, "\n";
          DFS(a1, v, seen + { v }, maxIter - 1);
        }
    }

    match Succ(s1, a1.tr, true) {
      case None =>  //    Done

      case Some(v) =>
        if v !in seen && maxIter > 0 {
          print "s", s1, " -- true -> ", "s", v, "\n";
          DFS(a1, v, seen + { v }, maxIter - 1);
        }
    }
  }

  function DFS2(a1: ValidAuto, s1: nat := 0, seen: set<nat> := {}, maxDepth: nat): (seq<(nat, bool, nat)>)
    decreases maxDepth
  {
    if s1 in seen || maxDepth == 0 then []
    else
      //  DFS false
      var leftSucc := Succ(s1, a1.tr, false);
      var leftBranch :=
        if leftSucc.Some? then
          var l := DFS2(a1, leftSucc.v, seen + { s1 }, maxDepth - 1);
          [(s1, false, leftSucc.v)] + l
        else [];

      //  DFS right
      var rightSucc := Succ(s1, a1.tr, true);
      var rightBranch :=
        if rightSucc.Some? then
          var r := DFS2(a1, rightSucc.v, seen + { s1 }, maxDepth - 1);
          [(s1, true, rightSucc.v)] + r
        else [];
      leftBranch + rightBranch
  }

  lemma foo606(s: set<nat>, k: nat)
    requires forall e:: e in s ==> e <= k
    ensures |s| <= k + 1
  {
    if |s| == 0 {

    } else {
      if k == 0 {
        assert s == { 0 };
      }
      else if k in s {
        foo606(s - { k }, k - 1);
      } else {
        var e: nat :| e in s;
        assert e <= k - 1;
        foo606(s - { e }, k - 1);
      }
    }
  }

  function DFS3(a1: ValidAuto, s1: nat := 0, seen: set<nat> := {}): (seq<(nat, bool, nat)>)
    // decreases maxDepth
    requires forall k:: k in seen ==> k < a1.numStates
    requires |seen| <= a1.numStates + 1 //  Not necessary to explicitly add this one
    decreases a1.numStates - |seen|
  {
    if s1 in seen then []
    else
      //  DFS false
      var leftSucc := Succ(s1, a1.tr, false);
      var leftBranch :=
        if leftSucc.Some? then
          foo606(seen + {s1}, a1.numStates);
          assert |seen + {s1}| > |seen|;
          var l := DFS3(a1, leftSucc.v, seen + { s1 });
          [(s1, false, leftSucc.v)] + l
        else [];

      //  DFS right
      var rightSucc := Succ(s1, a1.tr, true);
      var rightBranch :=
        if rightSucc.Some? then
          foo606(seen + {s1}, a1.numStates);
          assert |seen + {s1}| > |seen|;
          var r := DFS3(a1, rightSucc.v, seen + { s1 });
          [(s1, true, rightSucc.v)] + r
        else [];
      leftBranch + rightBranch
  }


  predicate IsBounded<T>(s: set<T>, k: nat)
  {
    |s| <= k
  }

  lemma foo202<T>(s: set<T>, u: set<T>, k: nat)
    requires IsBounded(s, k)
    requires u <= s
    ensures IsBounded(u, k)
  {
    if s != {} && s != u {
        var e :| e in s && e !in u;
        foo202(s - {e}, u, k - 1);
    }
  } 

  function DFS4(a1: ValidAuto, s1: nat := 0, seen: set<nat> := {}): (seq<(nat, bool, nat)>)
    // decreases maxDepth
    requires forall k:: k in seen ==> k < a1.numStates
    requires |seen| <= a1.numStates + 1 //  Not necessary to explicitly add this one
    decreases a1.numStates - |seen|
  {
    if s1 in seen then []
    else
      //  DFS false
      var leftSucc := Succ(s1, a1.tr, false);
      var leftBranch :=
        if leftSucc.Some? then
          foo606(seen + {s1}, a1.numStates);
          assert |seen + {s1}| > |seen|;
          var l := DFS3(a1, leftSucc.v, seen + { s1 });
          [(s1, false, leftSucc.v)] + l
        else [];

      //  DFS right
      var rightSucc := Succ(s1, a1.tr, true);
      var rightBranch :=
        if rightSucc.Some? then
          foo606(seen + {s1}, a1.numStates);
          assert |seen + {s1}| > |seen|;
          var r := DFS3(a1, rightSucc.v, seen + { s1 });
          [(s1, true, rightSucc.v)] + r
        else [];
      leftBranch + rightBranch
  }

  method {:main} Main() {
    var tr1 := map[ (0, true) := 1, (1, false) := 0, (0, false) := 2, (2, true) := 0];
    var a1: ValidAuto := Auto(3, tr1);

    // DFS(a1, 0, {}, 10);

    var r := DFS3(a1);
    PrintToDot(r);

  }

  method PrintEdges(xe: seq<(nat, bool, nat)>) {
    if |xe| > 0 {
      print "s", xe[0].0, " -> s", xe[0].2, " [label=", xe[0].1, "]\n";
      PrintEdges(xe[1..]);
    }
  }

  method PrintToDot(xe: seq<(nat, bool, nat)>) {
    print "digraph CFG", "\n";
    print "{", "\n";
    PrintEdges(xe);
    print "}", "\n";

  }

}