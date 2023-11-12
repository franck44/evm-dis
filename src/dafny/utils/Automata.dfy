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

  type ValidAuto = a: Auto | a.IsValid() witness Auto(0, map[])

  datatype Auto = Auto(numStates: nat, transitions: map<(nat, bool), nat>)
  {

    /** 
      * The transition function should return states within the numStates range.
      * Note that the map can have keys (k, l) with states k >= numStates, that's
      * perfectly accpetable.
      */
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

}