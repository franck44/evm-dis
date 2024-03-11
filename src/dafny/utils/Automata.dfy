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
      ensures i in a.states
      ensures forall s:: s in states ==> s in a.states
      ensures forall s:: s in a.states ==> s in states || s == i
      ensures i in states ==> a == this
      ensures i !in states ==> a.SSize() == SSize() + 1
      ensures i !in states ==> (forall s:: s in states ==> a.transitions[s] == transitions[s]) && a.transitions[i] == []
      ensures i !in states ==> a.transitionsNat[|states|] == []
      ensures i !in states ==> a.revTransitionsNat[|states|] == []
      ensures a.IsValid()
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

      ensures i in a.states
      ensures j in a.states
      ensures forall s:: s in states ==> s in a.states
      ensures forall s:: s in a.states ==> s in states || s == i || s == j
      ensures forall s:: s in a.states && s != i && s != j ==> s in a.transitions
      ensures forall s:: s in a.states && s != i && s != j ==> a.transitions[s] == transitions[s]
      ensures i in a.transitions
      ensures i in states ==> |a.transitions[i]| <= |transitions[i]| + 1
      ensures i !in states ==> a.transitions[i] == [j]
    {
      var a1 := this.AddState(i).AddState(j);
      if a1.indexOf[j] in a1.transitionsNat[a1.indexOf[i]] then
        assert j in a1.transitions[i];
        a1
      else
        AddEdgeInTRandTrNatPreservesValid(a1, i, j);
        var w := a1.(transitions := AddKeyVal(a1.transitions, i, j),
                 transitionsNat := AddKeyVal(a1.transitionsNat, a1.indexOf[i], a1.indexOf[j]),
                 revTransitionsNat := AddKeyVal(a1.revTransitionsNat, a1.indexOf[j], a1.indexOf[i]));
        w
    }

    /** A lemma to make verification of AddEdge easier. */
    static lemma {:timeLimitMultiplier 6} AddEdgeInTRandTrNatPreservesValid(a: ValidAuto<T>, i: T, j: T)
      requires a.IsValid()
      requires i in a.states
      requires j in a.states
      ensures a
              .(transitions := AddKeyVal(a.transitions, i, j))
              .(transitionsNat := AddKeyVal(a.transitionsNat, a.indexOf[i], a.indexOf[j]))
              .(revTransitionsNat := AddKeyVal(a.revTransitionsNat, a.indexOf[j], a.indexOf[i]))
              .IsValid()
    {
      var a1 := a.(transitions := AddKeyVal(a.transitions, i, j));
      ReverseMapsIsCongruent(a.transitionsNat, a.revTransitionsNat, a1.transitionsNat, a1.revTransitionsNat);
    }

    /**
      *  Add several transitions from i to all the elements of js.
      */
    function {:timeLimitMultiplier 6} {:opaque} AddEdges(i: T, js: seq<T>, index: nat := 0): (a: ValidAuto<T>)
      requires this.IsValid()
      requires index <= |js|
      requires forall j:: 0 <= j < index ==> js[j] in this.states
      ensures a.IsValid()
      ensures i in a.states
      ensures forall s:: s in this.states ==> s in a.states
      ensures forall j:: 0 <= j < |js| ==> js[j] in a.states
      ensures forall s:: s in a.states ==> s in this.states || s == i || s in js
      decreases |js| - index
    {
      if |js| == index then
        this.AddState(i)
      else
        var a1: ValidAuto<T> := this.AddEdge(i, js[index]);
        assert i in a1.states;
        assert js[index] in a1.states;
        assert a1.IsValid();
        assert  forall j:: 0 <= j < index  ==> js[j] in a1.states;
        assert js[index] in a1.states;
        ExtendByOneGoodIsGood(index, js, i => i in a1.states);
        assert forall j:: 0 <= j < index + 1 ==> js[j] in a1.states;
        var a2 := a1.AddEdges(i, js, index + 1);
        a2
    }

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

    /**
      *  The successors using the id of the states.
      *  @param      i  The id of the source state.
      *  @returns        The ids of the successors.
      */
    function {:opaque} PredNat(i: nat): (r: seq<nat>)
      requires this.IsValid()
      requires i < |states|
      ensures forall j: nat :: 0 <= j < |r| ==> r[j] < |states|
    {
      revTransitionsIsBounded();
      assert forall j: nat :: 0 <= j < |revTransitionsNat[i]| ==> revTransitionsNat[i][j] in revTransitionsNat[i];
      revTransitionsNat[i]
    }

    /**
      *  Given all the constraints in IsValid, 
      *  the predecessors must be in 0..|states| - 1.
      */
    lemma {:timeLimitMultiplier 2} revTransitionsIsBounded()
      requires this.IsValid()
      ensures forall k, v:: k in revTransitionsNat &&  v in revTransitionsNat[k] ==> v < |states|
    {
      forall k, v | k in revTransitionsNat.Keys && v in revTransitionsNat[k]
        ensures v < |states|
      {
        assert v in transitionsNat;
      }
    }

    /** Print to Dot format. */
    method {:print} ToDot(nodeToString: (T, nat) --> string, labelToString: (T, nat, T) --> string, prefix: string := "", name: string := "G")
      requires this.IsValid()
      requires forall s, k:: s in states ==> nodeToString.requires(s, k)
      requires forall s, s', n:: s in states && s' in states ==> labelToString.requires(s, n, s')
    {
      print "// Number of states: ", SSize(), "\n";
      print "// Number of transitions : ", TSize(), "\n";
      print "digraph G {\n";
      print prefix, "\n";
      for i := 0 to |states|
      {
        print "s_", i, " [label=", nodeToString(states[i], i) + "]\n";
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

    /**
      * Check if the automaton is valid.
      */
    ghost predicate IsValid() {
      && StatesTransValid()
      && IndexOfValid()
      && TransNatTransIsValid()
      && IsReverseMapValid()
    }

    /**
      *  1. Each state must have a seq (possibly empty) of successors.
      *  2. Each successor must be a state.No towo states are equal. That means the seq
      *  is similar to a set.
      *  3. The successor states must be in the set of states.
      */
    ghost predicate StatesTransValid() {
      && (forall i : T :: i in states <==> i in transitions)
      && (forall k, k':: 0 <= k < k' < |states| ==> states[k] != states[k'])
      && (forall i, j :: i in states && 0 <= j < |transitions[i]| ==> transitions[i][j] in states)
    }

    /**
      * The index of a state is the position of the state in the seq of states.
      * The indexOf maap must be in sycn with states
      *
      */
    ghost predicate IndexOfValid()
    {
      && (forall s:: s in states <==> s in indexOf)
      && (forall i:: i in indexOf ==> indexOf[i] < |states| && states[indexOf[i]] == i)
      && (forall i:: 0 <= i < |states| ==> states[i] in indexOf && indexOf[states[i]] == i)
      && (indexOf.Values == set z {:nowarn} | 0 <= z < |states|)
      && (indexOf.Values == transitionsNat.Keys)
      && (indexOf.Values == revTransitionsNat.Keys)
    }

    /**
      * The transitionNat map must be in sync with the transitions map.
      */
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

    /**
      *  The map that gives the transitions in reverse must be in one-to-one
      *  correspondence with the transitionsNat map.
      */
    ghost predicate IsReverseMapValid()
    {
      && (forall src, tgt:: src in transitionsNat && tgt in transitionsNat[src]
                            <==> tgt in revTransitionsNat && src in revTransitionsNat[tgt])
    }
  }
}