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
module AutomataV2 {

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
    *  @toString                The string representation of a state.
    *  @indexOf                 The index of a state.
    *  @note                    A valid automaton is such that every state has an entry in the transitions map.
    *                           If the state has no successor then the entry is the empty list.
    *  @note                    The transition function is givem as transitionsNat, but the datatype
    *                           uses transitions which is a map from stateId to stateIds. The reason
    *                           is that it is easier to manipulate the transitions using the stateId .e.g.
    *                           when minising an automaton.
    */
  datatype Auto<!T(!new,==)> =
    Auto(ghost transitions: map<T, seq<T>> := map[],
         transitionsNat: map<nat, seq<nat>> := map[],
         states: seq<T> := [],
         toString: T -> string := (_  => ""),
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
    function {:timeLimitMultiplier 8} AddState(i: T): (a: Auto<T>)
      requires IsValid()
      ensures i in a.states
      ensures a.IsValid()
    {
      if i in states then
        this
      else
        assert (indexOf + map[i := |states|]).Values == indexOf.Values + { |states| };
        this
        .(states := states + [i])
        .(indexOf := indexOf + map[i := |states|])
        .(transitions := transitions + map[i := []])
        .(transitionsNat := transitionsNat + map[|states| := []])
    }

    /**
      * Add a transition from i to j to the automaton.
      * @param i  The source state.
      * @param j  The destination state.
      * @returns  An automaton with the transition added.  
      * @note     If i or j are not in the automaton then they are added.
      * @note     The transitions from i to j are in a seq, and j is added at the end of the seq.
      */
    function {:timeLimitMultiplier 8} AddEdge(i: T, j: T): (a: Auto<T>)
      requires IsValid()
      ensures a.IsValid()
    {
      var a1 := this.AddState(i).AddState(j);
      if a1.indexOf[j] in a1.transitionsNat[a1.indexOf[i]] then
        a1
      else
        a1
        .(transitions := a1.transitions + map[i := a1.transitions[i] + [j]])
        .(transitionsNat := a1.transitionsNat + map[a1.indexOf[i] := a1.transitionsNat[a1.indexOf[i]] + [a1.indexOf[j]]])
    }

    /**
      *  Add several transitions from i to all the elements of js.
      */
    function AddEdges(i: T, js: seq<T>): (a: Auto<T>)
      requires IsValid()
      ensures a.IsValid()
      decreases |js|
    {
      if |js| == 0 then this
      else this.AddEdge(i, js[0]).AddEdges(i, js[1..])
    }

    /**
      * Returns the number of states of the automaton.
      */
    function SSize(): nat
      requires this.IsValid()
    {
      |states|
    }

    function TSize(index: nat := 0): nat
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
    function Succ(s: T): (r: seq<T>)
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
    function SuccNat(i: nat): (r: seq<nat>)
      requires this.IsValid()
      requires i < |states|
      ensures forall j: nat :: 0 <= j < |r| ==> r[j] < |states|
    {
      transitionsNat[i]
    }

    /**
      * String representation of a state.
      */
    function ToString(t: T): string {
      toString(t)
    }

    /** Print to Dot format. */
    method {:print} ToDot()
      requires this.IsValid()
    {
      print "digraph G {\n";
      print "// Number of states: ", NatToString(SSize()), "\n";
      print "// Number of transitions : ", NatToString(TSize()), "\n";
      for i := 0 to |states|
      {
        print "s_", i, " [label=", ToString(states[i]) + "]\n";
      }
      for i := 0 to |states| {
        for j := 0 to |transitionsNat[i]| {
          print "s_", i, " -> ", "s_", transitionsNat[i][j],
                " [label=\"" + NatToString(j) + "\"]"
                + ";\n";
        }
      }
      print "}\n";
    }

    /**
      * Check if the automaton is valid.
      */
    ghost predicate IsValid() {
      && (forall i : T :: i in states <==> i in transitions)
      && (forall k, k':: 0 <= k < k' < |states| ==> states[k] != states[k'])
      && (forall i, j :: i in states && 0 <= j < |transitions[i]| ==> transitions[i][j] in states)
      && (forall s:: s in states <==> s in indexOf)
      && (forall i:: i in indexOf ==> indexOf[i] < |states| && states[indexOf[i]] == i)
      && (forall i:: 0 <= i < |states| ==> states[i] in indexOf && indexOf[states[i]] == i)
      && (indexOf.Values == set z {:nowarn} | 0 <= z < |states|)
      && (transitionsNat.Keys == set z {:nowarn} | 0 <= z < |states|)
      && (indexOf.Values == transitionsNat.Keys)
      && (forall k:: k in transitionsNat ==> |transitionsNat[k]| == |transitions[states[k]]|)
      && (forall k:: k in transitions ==> |transitions[k]| == |transitionsNat[indexOf[k]]|)
      && (forall i, j :: 0 <= i < |states| && 0 <= j < |transitionsNat[i]| ==> 0 <= transitionsNat[i][j] < |states|)
      && ((forall i, j :: 0 <= i < |states| && 0 <= j < |transitionsNat[i]| ==> states[transitionsNat[i][j]] == transitions[states[i]][j]))
      && ((forall i:T , j :: i in states && 0 <= j < |transitions[i]| ==> indexOf[transitions[i][j]] == indexOf[transitions[i][j]]))
    }
  }
}