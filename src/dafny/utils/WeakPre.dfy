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

include "./int.dfy"
include "./MiscTypes.dfy"
include "./StackElement.dfy"
  // include "./Instructions.dfy"

/**
  * Provides conditions/predicates of a given type.
  *
  * A Wpre is a constraint of the form pc == a && Peek(k) == b.
  * There can be many Peek(k) == b refering to several stack elements. 
  */
module WeakPre {

  import opened Int
  import opened MiscTypes
  import opened StackElement

  type ValidCond = c: Cond | c.IsValid() witness StCond([], [])

  /** Wpre */
  datatype Cond =
      StTrue()
    | StFalse()
    | StCond(trackedPos: seq<nat>, trackedVals: seq<u256>) {

    //  Helpers
    predicate IsValid() {
      this.StCond? ==>
        (
          && |trackedPos| == |trackedVals|
          && (forall k, k':: 0 <= k < k' < |trackedPos| ==> trackedPos[k] != trackedPos[k'])
        )
    }

    function TrackedPos(): seq<nat>
      requires IsValid()
      requires StCond?
    {
      trackedPos
    }

    function TrackedVals(): seq<u256>
      requires IsValid()
      requires StCond?
    {
      trackedVals
    }

    function TrackedPosAt(i: nat): nat
      requires IsValid()
      requires StCond?
      requires i < this.Size()
    {
      trackedPos[i]
    }

    function TrackedValAt(i: nat): u256
      requires IsValid()
      requires StCond?
      requires i < this.Size()
    {
      trackedVals[i]
    }

    function Size(): nat
      requires IsValid()
      requires StCond?
    {
      |trackedPos|
    }

    function Add(pos: u256, val: u256): (c' :Cond)
      requires IsValid()
      ensures c'.IsValid()
    {
      this
    }
  }
}
