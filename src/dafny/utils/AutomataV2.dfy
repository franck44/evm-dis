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

/** 
  * Provides finite automata.
  */
module AutomataV2 { 

  import opened MiscTypes
  import opened Int

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
      for i := 0 to |states| {
        print ToString(states[i]) + ";\n";
      }
      for i := 0 to |states| {
        for j := 0 to |Succ(states[i])| {
          print ToString(states[i]) + " -> " + ToString(transitions[states[i]][j]) +
                "[label=\"" + NatToString(j) + "\"]"
                + ";\n";
        }
      }
      print "}\n";
    }

    /** 
      *  Check that the automaton is well formed.
      *  @note   A well-formed automaton is such that every state has an entry in the transitions map.
      *          If the state has no successor then the entry is the empty list.
      */
    ghost predicate IsValid() {
      && (forall i : T :: i in states <==> i in transitions)
    }
  }
}