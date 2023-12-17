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

  type NatAuto = a: ValidAuto2<nat> | a.states == seq(|a.states|, i => i) witness Auto(_ => "")

  type ValidAuto2<!T(!new)> = a: Auto<T> | a.IsValid() witness Auto(_ => "", map[])



  /**
    *  Automaton.
    *  @param toString     The string representation of a state.
    *  @param transitions  The transition function.
    *  @param states       The set of states.
    *  @note               A valid automaton is such that every state has an entry in the transitions map.
    *                      If the state has no successor then the entry is the empty list.
    */
  datatype Auto<!T(!new,==)> = Auto(toString: T -> string, transitions: map<T, seq<T>> := map[], states: seq<T> := [])
  {
    predicate Equals(b: Auto<T>) {
      && transitions == b.transitions
      && states == b.states
    }

    /** Each state in states is mapped to its index.
      * The transitions are also mapped to nat -> seq<nat>.
      */
    function ToNatAuto(index: nat := 0, a: NatAuto := Auto(_ => "")): (a': NatAuto)
      requires this.IsValid()
      ensures a'.IsValid()
    {
      var k := StatesToIndex();
      // add transitions from index
      //   a.addEdges(index, transitions[index])
      //   a.addEdges(index, transitions[index])
      a
    }

    function addEdges(i: T, xj: seq<T>): (a: Auto<T>)
      requires this.IsValid()
      ensures a.IsValid()
      decreases |xj|
    {
      if xj == [] then this
      else this.addEdge(i, xj[0]).addEdges(i, xj[1..])
    }

    function addEdge(i: T, j: T): (a: Auto<T>)
      requires IsValid()
      ensures a.IsValid() 
    {
      if i in transitions then
        if j in transitions[i] then
          this
        else
          this
          .(transitions := transitions[i := transitions[i] + [j]] + (if j !in states then map[j := []] else map[]))
          .(states  := states + (if j in states then [] else [j]))
      else
        assert i !in states;
        if j in states || j == i then
          this
          .(transitions := transitions + map[i := [j]])
          .(states := states + [i])
        else
          assert j !in states;
          assert i !in states;
          this
          .(transitions := transitions + map[i := [j]] + map[j := []])
          .(states := states + [i, j])
    }

    /**
      * Returns the number of states of the automaton.
      */
    function SSize(): nat
      requires this.IsValid()
    {
      |states|
    }

    /** Number of transitions of the automaton. */
    function TSize(xd: seq<T> := states): nat
      requires this.IsValid()
      requires (forall i : T :: i in xd ==> i in transitions)
    {
      if xd == [] then 0
      else
        assert xd[0] in states;
        |transitions[xd[0]]| + TSize(xd[1..])
    }

    /** 
      *  Successors of a state.
      *  @param s  The state.
      */
    function Succ(s: T): seq<T>
      requires this.IsValid()
      requires s in states
    {
      transitions[s]
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
      var m: map<T, nat> := map[];
      //   ghost var k: set<K> := {};
      for i := 0 to |states|
        invariant forall k :: 0 <= k < i ==> states[k] in m
      {
        print "s_", i, " [label=", ToString(states[i]) + "]\n";
        m := m + map[states[i] := i];
      }
      assert forall k:: 0 <= k < |states| ==> states[k] in m;
      for i := 0 to |states| {
        for j := 0 to |transitions[states[i]]| {
          //   assume transitions[states[i]][j] in states;
          print "s_", i, " -> ", "s_", m[transitions[states[i]][j]],
                " [label=\"" + NatToString(j) + "\"]"
                + ";\n";
        }
      }
      print "}\n";
    }

    function StatesToIndex(m: map<T, nat> := map[], index: nat := 0) : (r: map<T, nat>)
      requires index <= |states|
      requires forall k:: k in m ==> 0 <= m[k] < index
      requires forall i:: i in m ==> m[i] < index && states[m[i]] == i
      requires forall k, k':: 0 <= k < k' < |states[index..]| ==> states[index..][k] != states[index..][k']
      requires forall k:: k in m <==> k in states[..index] && k !in states[index..]

      requires forall k:: k in m.Values <==> 0 <= k < index
      requires m.Values == set z {:nowarn} | 0 <= z < index
      requires forall i:: 0 <= i < index ==> states[i] in m && m[states[i]] == i

      ensures forall i:: i in r ==> r[i] < |states| && states[r[i]] == i
      ensures forall i:: 0 <= i < |states| ==> states[i] in r && r[states[i]] == i
      ensures r.Values == set z {:nowarn} | 0 <= z < |states|

      decreases |states| - index
    {
      if index == |states| then m
      else
        assert index !in m.Values;
        assert states[index] !in m;
        assert (m + map[states[index] := index]).Values == m.Values + { index  };
        StatesToIndex(m + map[states[index] := index], index + 1)
    }

    /** 
      *  Check that the automaton is well formed.
      *  @note   A well-formed automaton is such that every state has an entry in the transitions map.
      *          If the state has no successor then the entry is the empty list.
      */
    ghost predicate IsValid() {
      && (forall i : T :: i in states <==> i in transitions)
      && (forall k, k':: 0 <= k < k' < |states| ==> states[k] != states[k'])
      && (forall i, j :: i in states && 0 <= j < |transitions[i]| ==> transitions[i][j] in states)
    }
  }
}