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
include "./Partition.dfy"

/** 
  * Provides finitie automata.
  */
module Automata {

  import opened MiscTypes
  import opened PartitionMod

  //   datatype Node<T> =
  //       Num(index: nat, prop: T)
  //     | Sink()

  //   datatype Edge<U, T> = Edge(src: U, lab: U, tgt: T)

  /** Deterministic transition relation. 
    *
    *   0 is the starting state. A sink state is a state that is not
    *   in the map.   
    */
  //   type Transitions = map<(nat, bool), nat>

  //   type Transitions2<T(==)> = map<(T, bool), T>

  //   datatype Auto = Auto(numStates: nat, tr: Transitions, final: nat := 0)

  //   datatype Auto2<T> = Auto2(init: T, tr: Transitions2<T>, refSet: set<T>, bound: nat)

  //   type ValidAuto2 = a: Auto2<nat> | IsBounded(a.refSet, a.bound) witness Auto2(0, map[], {}, 0)

  //   type ValidAuto = a: Auto |
  //       && forall k:: k in a.tr.Keys ==> k.0 < a.numStates
  //                                        && forall k:: k in a.tr.Values ==> k < a.numStates
  //     witness Auto(0, map[], 0)

  //   state -> list of labels (enabled)
  //  state and for each l in list of labels -> state

  //  states = ["toto", "titi"] numbered from 0 to n
  //  labels same: ["l0", "l1", ] numbered from 0 to k
  //  transitions: if "titi" -- l -> "toto" then write it as 1 - i -> 0
  //  each l in labels[i] give the labels enables in states[i]

  type ValidAuto = a: Auto | a.IsValid() witness Auto(0, map[])

  //   type NatAuto = ValidAuto<nat, bool> // witness Auto([], [], map[])

  type ValidPair = p: Pair | p.IsValid() witness Pair(Auto(1, map[]), Partition(1, [{0}]))

  datatype Auto = Auto(numStates: nat, transitions: map<(nat, bool), nat>)
  {

    predicate IsValid()
    {
      forall k:: k in transitions ==> transitions[k] < numStates
    }

    /**
      *  Successor state of s via l.
      *  @param  s   A state index.
      *  @param  l   A label index.
      *  @returns    The successor of s via l if exists of None otherwise.      
      */
    function Succ(s: nat, l: bool): Option<nat>
      requires this.IsValid()
      requires 0 <= s < numStates
      ensures Succ(s, l).Some? ==> 0 <= Succ(s, l).v < numStates
    {
      if (s, l) in transitions then Some(transitions[(s, l)])
      else None
    }

  }

  datatype Pair = Pair(a: ValidAuto, p: ValidPartition) {

    predicate IsValid()
    {
      a.numStates == p.n
    }

    function Refine(): ValidPartition
        requires this.IsValid()
    {
        p
    }

  }



}