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
include "../utils/int.dfy"
include "../utils/LinSegments.dfy"

/** 
  * Provides finite automata.
  */
module Automata {

  import opened MiscTypes
  import opened Int
  import opened LinSegments

  /** A valid automaton satisfies some invariants given by IsValid(). */
  type ValidAuto<!T(!new)> = a: Auto<T> | a.IsValid() witness Auto()

  /**
    *  Automaton.
    *  @param transitions       The transition function.
    *  @param transitionsNat    The transition function using the id of the states.
    *  @param states            The set of states.
    *  @indexOf                 The index of a state.
    *  @note                    A valid automaton is such that every state has an entry in the transitions map.
    *                           If the state has no successor then the entry is the empty list.
    *  @note                    The transition function is given as transitionsNat, but the datatype
    *                           uses transitions which is a map from stateId to stateIds. The reason
    *                           is that it is easier to manipulate the transitions using the stateId .e.g.
    *                           when minising an automaton.
    */
  datatype Auto<!T(!new,==)> =
    Auto(ghost transitions: map<T, seq<T>> := map[],
         transitionsNat: map<nat, seq<nat>> := map[],
         revTransitionsNat: map<nat, seq<nat>> := map[],
         states: seq<T> := [],
         indexOf: map<T, nat> := map[])
  {
    predicate Equals(b: Auto<T>)
    {
      && transitionsNat == b.transitionsNat
      && states == b.states
    }

    /**
      * Add a state to the automaton.
      * @param i  The state to add.
      */
    function {:timeLimitMultiplier 8} {:opaque} AddState(i: T): (a: ValidAuto<T>)
      requires IsValid()
      requires IsReversemapValid()
      ensures i in a.states
      ensures forall s:: s in states ==> s in a.states
      ensures forall s:: s in a.states ==> s in states || s == i
      ensures i in states ==> a == this
      ensures i !in states ==> a.SSize() == SSize() + 1
      ensures i !in states ==> (forall s:: s in states ==> a.transitions[s] == transitions[s]) && a.transitions[i] == []
      ensures i !in states ==> a.transitionsNat[|states|] == []
      ensures i !in states ==> a.revTransitionsNat[|states|] == []
      ensures a.IsValid()
      ensures a.IsReversemapValid()
    {
      if i in states then
        this
      else
        assert i !in indexOf;
        assert (indexOf + map[i := |states|]).Values == indexOf.Values + { |states| };
        assert indexOf[i := |states|] == indexOf + map[i := |states|];
        this.(
        states := states + [i],
        indexOf := indexOf[i := |states|],
        transitions := transitions[i := []],
        transitionsNat := transitionsNat[|states| := []],
        revTransitionsNat := revTransitionsNat[|states| := []])
    }

    /**
      * Add several states to the automaton.
      */
    function {:opaque} AddStates(xs: seq<T>): (a: ValidAuto<T>)
      requires IsValid()
      requires IsReversemapValid()
      ensures a.IsValid()
      ensures forall s:: s in states ==> s in a.states
      ensures forall j:: 0 <= j < |xs| ==> xs[j] in a.states
      ensures forall s:: s in a.states ==> s in states || s in xs
      decreases |xs|
    {
      if |xs| == 0 then this
      else this.AddState(xs[0]).AddStates(xs[1..])
    }

    /**
      * Add a transition from i to j to the automaton.
      * @param i  The source state.
      * @param j  The destination state.
      * @returns  An automaton with the transition added.  
      * @note     If i or j are not in the automaton then they are added.
      * @note     The transitions from i to j are in a seq, and j is added at the end of the seq.
      */
    function {:timeLimitMultiplier 8} {:opaque} AddEdge(i: T, j: T): (a: ValidAuto<T>)
      requires IsValid()
      requires IsReversemapValid()

      ensures i in a.states
      ensures j in a.states
      ensures forall s:: s in states ==> s in a.states
      ensures forall s:: s in a.states ==> s in states || s == i || s == j
      ensures forall s:: s in a.states && s != i && s != j ==> s in a.transitions
      ensures forall s:: s in a.states && s != i && s != j ==> a.transitions[s] == transitions[s]
      ensures i in a.transitions
      ensures i in states ==> |a.transitions[i]| <= |transitions[i]| + 1
      ensures i !in states ==> a.transitions[i] == [j]
      ensures a.IsReversemapValid()
    {
      var a1 := this.AddState(i).AddState(j);
      if a1.indexOf[j] in a1.transitionsNat[a1.indexOf[i]] then
        assert j in a1.transitions[i];
        a1
      else
        AddEdgeInTRandTrNatPreservesValid(a1, i, j);
        var w := a1.(transitions := AddKeyVal2(a1.transitions, i, j),
                 transitionsNat := AddKeyVal(a1.transitionsNat, a1.indexOf[i], a1.indexOf[j]),
                 revTransitionsNat := AddKeyVal(a1.revTransitionsNat, a1.indexOf[j], a1.indexOf[i]));
        w
    }

    /** A lemma to make verification of AddEdge easier. */
    lemma {:timeLimitMultiplier 6} AddEdgeInTRandTrNatPreservesValid(a: ValidAuto<T>, i: T, j: T)
      requires a.IsValid()
      requires a.IsReversemapValid()
      requires i in a.states
      requires j in a.states
      ensures a
              .(transitions := AddKeyVal2(a.transitions, i, j))
              .(transitionsNat := AddKeyVal(a.transitionsNat, a.indexOf[i], a.indexOf[j]))
              .(revTransitionsNat := AddKeyVal(a.revTransitionsNat, a.indexOf[j], a.indexOf[i]))
              .IsValid()
      ensures var a1 := a
                        .(transitions := AddKeyVal2(a.transitions, i, j),
                        transitionsNat := AddKeyVal(a.transitionsNat, a.indexOf[i], a.indexOf[j]),
                        revTransitionsNat := AddKeyVal(a.revTransitionsNat, a.indexOf[j], a.indexOf[i]));
              a1.IsReversemapValid()
    {
      var a1 := a.(transitions := AddKeyVal2(a.transitions, i, j));
      assert a1.transitionsNat == a.transitionsNat;
      assert a1.revTransitionsNat == a.revTransitionsNat;
      foo303(a, a1);
      assert a1.IsReversemapValid();
      var a2 := a1.(
      transitionsNat := AddKeyVal(a1.transitionsNat, a.indexOf[i], a.indexOf[j]),
      revTransitionsNat := AddKeyVal(a1.revTransitionsNat, a.indexOf[j], a.indexOf[i]));
      assert a2.transitionsNat == AddKeyVal(a1.transitionsNat, a.indexOf[i], a.indexOf[j]);
      assert a2.revTransitionsNat == AddKeyVal(a1.revTransitionsNat, a.indexOf[j], a.indexOf[i]);
      foo(a1.transitionsNat, a1.revTransitionsNat, a.indexOf[i], a.indexOf[j]);
      assert a2.IsReversemapValid();
    }

    // lemma {:timeLimitMultiplier 2} foo202(i: T, j: T)
    //   requires i in transitions
    //   requires j in transitions
    //   requires IsReversemapValid()
    //   ensures
    //     var a1 := this.(transitions := AddKeyVal2(this.transitions, i, j));
    //     a1.IsReversemapValid()
    // {
    //   var a1 := this.(transitions := AddKeyVal2(this.transitions, i, j));
    //   assert a1.transitionsNat == this.transitionsNat;
    //   assert a1.revTransitionsNat == this.revTransitionsNat;
    //   foo303(this, a1);
    //   assert a1.IsReversemapValid();

    // }

    static lemma foo303(a: Auto<T>, b: Auto<T>)
      requires a.IsReversemapValid()
      requires a.transitionsNat == b.transitionsNat
      requires a.revTransitionsNat == b.revTransitionsNat
      ensures b.IsReversemapValid()
    {
      forall src, tgt | src in b.transitionsNat && tgt in b.transitionsNat[src]
        ensures tgt in b.revTransitionsNat && src in b.revTransitionsNat[tgt]
      {
        assert tgt in a.revTransitionsNat && src in a.revTransitionsNat[tgt];
        assert a.revTransitionsNat == b.revTransitionsNat;
        assert tgt in b.revTransitionsNat && src in b.revTransitionsNat[tgt];
      }
      forall src, tgt | src in b.revTransitionsNat && tgt in b.revTransitionsNat[src]
        ensures tgt in b.transitionsNat && src in b.transitionsNat[tgt]
      {
        assert tgt in a.transitionsNat && src in a.transitionsNat[tgt];
        assert a.transitionsNat == b.transitionsNat;
        assert tgt in b.transitionsNat && src in b.transitionsNat[tgt];
      }
    }

    static lemma foo(m: map<nat, seq<nat>>, m': map<nat, seq<nat>>, i: nat, j: nat)
      //   requires m.Keys == m'.Keys
      requires i in m
      requires j in m
      requires IsReversemap(m, m')
      ensures IsReversemap(AddKeyVal(m, i, j), AddKeyVal(m', j, i))
    {

    }

    // static lemma foo2<T(==)>(m: map<T, seq<T>>, m': map<T, seq<T>>, i: T, j: T)
    //   requires m.Keys == m'.Keys
    //   requires i in m
    //   requires j in m
    //   requires IsReversemap2(m, m')
    //   ensures IsReversemap2(AddKeyVal2(m, i, j), AddKeyVal2(m', j, i))
    // {

    // }

    static function AddKeyVal(m: map<nat, seq<nat>>, key: nat, val: nat): (m': map<nat, seq<nat>>)
      requires key in m
    {
      m[key := m[key] + [val]]
    }

    static function AddKeyVal2<T(==)>(m: map<T, seq<T>>, key: T, val: T): (m': map<T, seq<T>>)
      requires key in m
      requires val in m
    {
      m[key := m[key] + [val]]
    }


    /**
      *  Add several transitions from i to all the elements of js.
      */
    function {:timeLimitMultiplier 6} {:opaque} AddEdges(i: T, js: seq<T>, index: nat := 0): (a: ValidAuto<T>)
      requires this.IsValid()
        requires IsReversemapValid()
      requires index <= |js|
      requires forall j:: 0 <= j < index ==> js[j] in this.states
      ensures a.IsValid()
      ensures a.IsReversemapValid()
      ensures i in a.states
      ensures forall s:: s in this.states ==> s in a.states
      ensures forall j:: 0 <= j < |js| ==> js[j] in a.states
      ensures forall s:: s in a.states ==> s in this.states || s == i || s in js
      decreases |js| - index
    {
    //   assume this.IsReversemapValid();
      if |js| == index then
        this.AddState(i)
      else
        // assume this.AddEdge.requires(i, js[index]);
        var a1: ValidAuto<T> := this.AddEdge(i, js[index]);
        assert i in a1.states;
        assert js[index] in a1.states;
        assert a1.IsValid();
        // // assume a1.IsReversemapValid();
        // assume a1.AddEdges.requires(i, js, index + 1);
        // assume a1.IsValid();
        assert  forall j:: 0 <= j < index  ==> js[j] in a1.states;
        assert js[index] in a1.states;
        foo404(index, js, a1.states);
        assert forall j:: 0 <= j < index + 1 ==> js[j] in a1.states;
        var a2 := a1.AddEdges(i, js, index + 1);
        // assume a2.IsValid();
        // assume a2.IsReversemapValid();
        // a2
        a2
    }

    static lemma foo404(index: nat, js: seq<T>, b: seq<T>)
      requires index < |js|
      requires  forall j:: 0 <= j < index  ==> js[j] in b
      requires js[index] in b
      ensures forall j:: 0 <= j < index + 1 ==> js[j] in b
    {

    }

    /**
      *  Add edges from each j in js to i 
      */
    // function {:timeLimitMultiplier 4} {:opaque} AddReverseEdges(i: T, js: seq<T>, index: nat := 0): (a: ValidAuto<T>)
    //   requires this.IsValid()
    //   requires index <= |js|
    //   requires forall j:: 0 <= j < |js| ==> js[j] in this.states
    //   requires i in states
    //   requires forall j:: 0 <= j < index ==> i in transitions[js[j]]
    //   //   requires forall j, tgt:: 0 <= j < index && tgt in transitions[states[j]] ==> (states[j] in transitions[tgt])

    //   ensures a.IsValid()
    //   ensures a.states == this.states
    //   ensures forall t:: t in a.transitions <==> t in this.transitions || (t in js && i in transitions[t])
    //   ensures forall j:: j in js ==> j in a.transitions
    //   ensures forall j:: 0 <= j < |js| ==> i in a.transitions[js[j]]
    //   //   ensures forall j, tgt:: 0 <= j < |js| && tgt in transitions[states[j]] ==> (states[j] in a.transitions[tgt])

    //   decreases |js| - index
    // {
    //   reveal_AddEdge();
    //   if |js| == index then this
    //   else
    //     var a1 := this.AddEdge(js[index], i);
    //     a1.AddReverseEdges(i, js, index + 1)
    // }

    // function {:timeLimitMultiplier 4} {:opaque} AddReverseEdges2(i: nat, js: seq<nat>, index: nat := 0): (a: Auto<T>)
    //   requires this.IsValid()
    //   requires i in transitionsNat
    //   requires index <= |js|
    // //   requires
    // //   requires forall j:: 0 <= j < |js| ==> js[j] in this.states
    // //   requires i in states
    // //   requires forall j:: 0 <= j < index ==> i in transitions[js[j]]
    // //   requires forall j, tgt:: 0 <= j < index && tgt in transitions[states[j]] ==> (states[j] in transitions[tgt])

    // //   ensures a.IsValid()
    //   ensures a.states == this.states
    // //   ensures forall t:: t in a.transitions <==> t in this.transitions || (t in js && i in transitions[t])
    // //   ensures forall j:: j in js ==> j in a.transitions
    // //   ensures forall j:: 0 <= j < |js| ==> i in a.transitions[js[j]]
    // //   ensures forall j, tgt:: 0 <= j < |js| && tgt in transitions[states[j]] ==> (states[j] in a.transitions[tgt])

    //   decreases |js| - index
    // {
    //   reveal_AddEdge();
    //   if index == |js| then this
    //   else
    //     // var forwardTrans := if indextransitionsNat[index] else [];
    //     var a1 := this.(transitionsNat := transitionsNat[index := transitionsNat[index] + [i]]);
    //     assume a1.IsValid();
    //     a1.AddReverseEdges2(i, js, index + 1)
    // }

    // function ReverseMap(m: map<nat, seq<nat>>, index: nat := 0): (m': map<nat, seq<nat>>)
    //   requires forall k:: k in m <==> 0 <= k < |m|
    // {
    //   m
    // }

    // function AddReverseEntries(m: map<nat, seq<nat>>, k: nat, xe: seq<nat>, b: nat): (m': map<nat, seq<nat>>)
    //   requires forall key:: key in m <==> 0 <= key < b
    //   requires forall i:: 0 <= i < |xe| ==> 0 <= xe[i] < b
    //   requires forall  key, i:: key in m && 0 <= i < |m[key]| ==> 0 <= m[key][i] < b
    //   requires k < b
    //   //  tuples of m are preserved
    //   ensures forall key, val:: key in m && val in m[key] ==> key in m' && val in m'[key]
    //   //  k is added to the tuples of xe
    //   ensures forall e:: e in xe ==> e in m' && k in m'[e]
    //   //  A key in m' is either in m or in xe
    //   ensures forall key:: key in m' <==> key in m || key in xe
    //   ensures forall key:: key in m' <==> 0 <= key < b
    //   ensures forall key, i:: key in m' && 0 <= i < |m'[key]| ==> 0 <= m'[key][i] < b

    //    //  A value in m' is either in m[key] or k
    //   ensures forall key, val:: key in m' && val in m'[key] <==> ((key in m && val in m[key]) || (val == k && key in xe))
    // {
    //   if |xe| == 0 then m
    //   else
    //     var m1 := m[xe[0] := m[xe[0]] + [k]];
    //     // assert forall key, val:: key in m && val in m[key] ==> key in m1 && val in m1[key];
    //     // assert forall key, i:: key in m1 && 0 <= i < |m1[key]| ==> 0 <= m1[key][i] < b;
    //     AddReverseEntries(m[xe[0] := m[xe[0]] + [k]], k, xe[1..], b)
    // }



    /**
      * Returns the number of states of the automaton.
      */
    function SSize(): nat
      requires this.IsValid()
    {
      |states|
    }

    /**
      *  The number of transitions.
      */
    function {:opaque} TSize(index: nat := 0): nat 
      requires this.IsValid()
      requires index <= |states|
      decreases |states| - index
    {
      if index == |states| then 0
      else
        |transitionsNat[index]| + TSize(index + 1)
    }

    /** 
      *  Successors of a state.
      *  @param s  The state.
      *  @returns  The successors of s.
      */
    function {:opaque} Succ(s: T): (r: seq<T>)
      requires this.IsValid()
      requires s in states
      ensures r == transitions[s]
    {
      seq(|transitionsNat[indexOf[s]]|, i requires 0 <= i < |transitionsNat[indexOf[s]]| => states[transitionsNat[indexOf[s]][i]])
    }

    /**
      *  The successors using the id of the states.
      *  @param      i  The id of the source state.
      *  @returns        The ids of the successors.
      */
    function {:opaque} SuccNat(i: nat): (r: seq<nat>)
      requires this.IsValid()
      requires i < |states|
      ensures forall j: nat :: 0 <= j < |r| ==> r[j] < |states|
    {
      transitionsNat[i]
    }

    /** Print to Dot format. */
    method {:print} ToDot(nodeToString: T --> string, labelToString: (T, nat, T) --> string, prefix: string := "", name: string := "G")
      requires this.IsValid()
      requires forall s:: s in states ==> nodeToString.requires(s)
      requires forall s, s', n:: s in states && s' in states ==> labelToString.requires(s, n, s')
    {
      print "// Number of states: ", SSize(), "\n";
      print "// Number of transitions : ", TSize(), "\n";
      print "digraph G {\n";
      print prefix, "\n";
      for i := 0 to |states|
      {
        print "s_", i, " [label=", nodeToString(states[i]) + "]\n";
      }
      for i := 0 to |states| {
        for j := 0 to |transitionsNat[i]| {
          print "s_", i, " -> ", "s_", transitionsNat[i][j],
                labelToString(states[i], j, states[transitionsNat[i][j]]),
                ";\n";
        }
      }
      print "}\n";
    }

    // function {:timeLimitMultiplier 2} ReverseAuto(index: nat := 0, a: ValidAuto<T>): (a': ValidAuto<T>)
    //   requires this.IsValid()
    //   requires index <= |states|
    //   requires a.states == states
    //   requires forall j, tgt:: 0 <= j < index && tgt in transitions[states[j]] ==> (states[j] in a.transitions[tgt])
    //   ensures a'.states == states
    //   //   ensures forall j, tgt:: j in  states && tgt in transitions[j] ==> (j in a'.transitions[tgt])
    //   ensures forall j, tgt:: 0 <= j < |states| && tgt in transitions[states[j]] ==> (states[j] in a'.transitions[tgt])

    //   decreases |states| - index
    // {
    //   //   reveal_AddReverseEdges();
    //   //   reveal_AddStates();
    //   if |states| == index then a
    //   else
    //     var aut2 := a.AddReverseEdges(
    //                   states[index],
    //                   MapP(transitionsNat[index], i requires i in transitionsNat[index] => states[i]));
    //     // assert forall j:: 0 <= j < |js| ==> i in a.transitions[js[j]];
    //     assume  forall j, tgt:: 0 <= j < index + 1 && tgt in transitions[states[j]] ==> (states[j] in aut2.transitions[tgt]);
    //     ReverseAuto(index + 1, aut2)
    // }

    /**
      * Check if the automaton is valid.
      */
    ghost predicate IsValid() {
      //   && (forall i : T :: i in states <==> i in transitions)
      //   && (forall k, k':: 0 <= k < k' < |states| ==> states[k] != states[k'])
      //   && (forall i, j :: i in states && 0 <= j < |transitions[i]| ==> transitions[i][j] in states)
      && StatesTransValid()

      //   && (forall s:: s in states <==> s in indexOf)
      //   && (forall i:: i in indexOf ==> indexOf[i] < |states| && states[indexOf[i]] == i)
      //   && (forall i:: 0 <= i < |states| ==> states[i] in indexOf && indexOf[states[i]] == i)
      //   && (indexOf.Values == set z {:nowarn} | 0 <= z < |states|)
      //   && (indexOf.Values == transitionsNat.Keys)
      && IndexOfValid()

      //   && (forall k:: k in transitionsNat ==> |transitionsNat[k]| == |transitions[states[k]]|)
      //   && (forall k:: k in transitions ==> |transitions[k]| == |transitionsNat[indexOf[k]]|)
      //   && (forall i, j :: 0 <= i < |states| && 0 <= j < |transitionsNat[i]| ==> 0 <= transitionsNat[i][j] < |states|)
      //   && ((forall i, j :: 0 <= i < |states| && 0 <= j < |transitionsNat[i]| ==> states[transitionsNat[i][j]] == transitions[states[i]][j]))
      //   && ((forall i:T , j :: i in states && 0 <= j < |transitions[i]| ==> indexOf[transitions[i][j]] == indexOf[transitions[i][j]]))
      && TransNatTransIsValid()

      //   && transitionsNat.Keys == revTransitionsNat.Keys
      //        && (forall src, tgt:: src in transitionsNat && tgt in transitionsNat[src]
      //                              ==> tgt in revTransitionsNat && src in revTransitionsNat[tgt])
      //   && (forall src, tgt:: src in revTransitionsNat && tgt in revTransitionsNat[src]
      //                         ==> tgt in transitionsNat && src in transitionsNat[tgt])
      //   && IsReversemap(transitionsNat, revTransitionsNat)
    }

    ghost predicate StatesTransValid() {
      && (forall i : T :: i in states <==> i in transitions)
      && (forall k, k':: 0 <= k < k' < |states| ==> states[k] != states[k'])
      && (forall i, j :: i in states && 0 <= j < |transitions[i]| ==> transitions[i][j] in states)
    }

    ghost predicate IndexOfValid()
    {
      && (forall s:: s in states <==> s in indexOf)
      && (forall i:: i in indexOf ==> indexOf[i] < |states| && states[indexOf[i]] == i)
      && (forall i:: 0 <= i < |states| ==> states[i] in indexOf && indexOf[states[i]] == i)
      && (indexOf.Values == set z {:nowarn} | 0 <= z < |states|)
      && (indexOf.Values == transitionsNat.Keys)
      && (indexOf.Values == revTransitionsNat.Keys)
    }

    ghost predicate TransNatTransIsValid()
      requires StatesTransValid()
      requires IndexOfValid()
    {
      && (forall k:: k in transitionsNat ==> |transitionsNat[k]| == |transitions[states[k]]|)
      && (forall k:: k in transitions ==> |transitions[k]| == |transitionsNat[indexOf[k]]|)
      && (forall i, j :: 0 <= i < |states| && 0 <= j < |transitionsNat[i]| ==> 0 <= transitionsNat[i][j] < |states|)
      && ((forall i, j :: 0 <= i < |states| && 0 <= j < |transitionsNat[i]| ==> states[transitionsNat[i][j]] == transitions[states[i]][j]))
      && ((forall i:T , j :: i in states && 0 <= j < |transitions[i]| ==> indexOf[transitions[i][j]] == indexOf[transitions[i][j]]))
    }

    ghost predicate IsReversemapValid()
    {
      //   && transitionsNat.Keys == revTransitionsNat.Keys
      && (forall src, tgt:: src in transitionsNat && tgt in transitionsNat[src]
                            <==> tgt in revTransitionsNat && src in revTransitionsNat[tgt])
    }

    ghost predicate IsReversemapValid2()
    {
      IsReversemap(transitionsNat, revTransitionsNat)
      //   && m.Keys == m'.Keys
      //   && (forall src, tgt:: src in m && tgt in m[src]
      //                         ==> tgt in m' && src in m'[tgt])
      //   && (forall src, tgt:: src in m' && tgt in m'[src]
      //                         ==> tgt in m && src in m[tgt])
    }

    static ghost predicate IsReversemap(m: map<nat, seq<nat>>, m': map<nat, seq<nat>>)
    {
      && m.Keys == m'.Keys
      && (forall src, tgt:: src in m && tgt in m[src]
                            <==> tgt in m' && src in m'[tgt])
         //   && (forall src, tgt:: src in m' && tgt in m'[src]
         //                         ==> tgt in m && src in m[tgt])
    }

    static ghost predicate IsReversemap2<T>(m: map<T, seq<T>>, m': map<T, seq<T>>)
    {
      && m.Keys == m'.Keys
      && (forall src, tgt:: src in m && tgt in m[src]
                            ==> tgt in m' && src in m'[tgt])
         //   && (forall src, tgt:: src in m' && tgt in m'[src]
         //                         ==> tgt in m && src in m[tgt])
    }

  }
}