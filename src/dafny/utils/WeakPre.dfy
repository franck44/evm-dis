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

  type ValidCond = c: Cond | c.IsValid() witness StCond([1], [0x00])

  /** Wpre */
  datatype Cond =
      StTrue()
    | StFalse()
    | StCond(trackedPos: seq<nat>, trackedVals: seq<u256>) {

    //  Helpers
    predicate IsValid() {
      this.StCond? ==>
        (
          && |trackedPos| == |trackedVals| > 0
          && (forall k, k':: 0 <= k < k' < |trackedPos| ==> trackedPos[k] != trackedPos[k'])
        )
    }

    /** Size of a condition. True and False have size zero. */
    function Size(): nat
    {
      if this.StCond? then |trackedPos|
      else 0
    }

    /**
      * And of two conditions, with check that similar positions
      * have the same constraints.
      */
    function {:opaque} And(c: ValidCond): ValidCond
      requires this.IsValid()
    {
      match (this, c)
      case (StFalse(), _) => StFalse()
      case (_, StFalse()) => StFalse()
      case (StTrue(), cond ) => cond
      case (c1, StTrue()) => c1
      case (c1, c2) => Merge(c1, c2)
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

    function Tail(): ValidCond
      requires this.IsValid()
      requires this.Size() > 1
    {
      this.(trackedPos := trackedPos[1..], trackedVals := trackedVals[1..])
    }

    function Add(pos: u256, val: u256): (c' :Cond)
      requires IsValid()
      ensures c'.IsValid()
    {
      this
    }

    /** Build stack that satifies this cond. */
    function BuildStack(r: seq<StackElem> := [], index: nat := 0): (s: seq<StackElem>)
      requires this.StCond?
      requires this.IsValid()
      requires index <= |trackedPos|
      decreases |trackedPos| - index
    {
      if index == |trackedPos|  then r
      else
      if trackedPos[index] < |r| then
        BuildStack(r[trackedPos[index] := Value(trackedVals[index])], index + 1)
      else
        //  we have to add a suffix of trackedPos[0] - |r| elements
        var suf := seq(trackedPos[index] - |r|, _ => Random());
        assert |r + suf + [Value(trackedVals[index])]| == trackedPos[index] + 1;
        BuildStack(r + suf + [Value(trackedVals[index])], index + 1)
    }

  }

  //   Helper

  /**
    *    Build a cond that captures a stack value 
    */
  function {:opaque} StackToCond(xs: seq<StackElem>): (c: ValidCond)
    ensures c.IsValid()
  {
    var r := StackToCondHelper(xs);
    if |r.0| == 0 then StTrue()
    else
      StCond(r.0, r.1)
  }

  function StackToCondHelper(xs: seq<StackElem>, c: (seq<nat>, seq<u256>) := ([], []), index: nat := 0): (r: (seq<nat>, seq<u256>))
    requires index <= |xs|
    requires |c.0| == |c.1|
    requires forall k, k':: 0 <= k < k' < |c.0| ==> c.0[k] < c.0[k']
    requires forall k:: 0 <= k < |c.0| ==> c.0[k] < index
    ensures |r.0| == |r.1|
    ensures forall k, k':: 0 <= k < k' < |r.0| ==> r.0[k] < r.0[k']
    ensures forall k, k':: 0 <= k < k' < |r.0| ==> r.0[k] != r.0[k']
    decreases |xs| - index
  {
    if |xs| == index then c
    else if xs[index].Value? then
      var c' := (c.0 + [index], c.1 + [xs[index].v]);
      StackToCondHelper(xs, c', index + 1)
    else
      StackToCondHelper(xs, c, index + 1)
  }


  /**
    *   Merge two conditions.
    *
    *   @returns    The condition that contains the trackedPos and 
    *               trackedValues of c1 and c2.
    *   @note       If a position is in c1 and c2 then the tracked values
    *               are checked. If they are equal that's good, otherwise
    *               the resukt is StFalse as they contain incompatible 
    *               constraints.
    */
  function Merge(c1: ValidCond, c2: ValidCond): (r: Cond)
    requires c1.StCond? && c2.StCond?
    ensures r.IsValid()
    decreases c2.Size()
  {
    if c2.Size() == 0 then c1
    else if c2.Size() == 1 then
      if c2.trackedPos[0] in c1.trackedPos then
        var i := FindVal(c2.trackedPos[0], c1.trackedPos);
        if  c1.trackedVals[i] == c2.trackedVals[0] then
          c1
        else
          StFalse()
      else StCond(c1.trackedPos + [c2.trackedPos[0]], c1.trackedVals + [c2.trackedVals[0]])
    else    // c2.Size() > 1;
      assert c2.Size() > 1;
      if c2.trackedPos[0] in c1.trackedPos then
        Merge(c1, StCond(c2.trackedPos[1..], c2.trackedVals[1..]))
      else
        var p := c1.trackedPos + [c2.trackedPos[0]];
        var v := c1.trackedVals + [c2.trackedVals[0]];
        Merge(StCond(p, v), StCond(c2.trackedPos[1..], c2.trackedVals[1..]))
  }

  /**
    *   Find the index of an element of a seq.
    *   @param  x   The element to locate.
    *   @param  xs  The seq the element is in.
    *   @returns    The index of the first occurrence of `x` in `xs`.
    */
  function FindVal<T(==)>(x: T, xs: seq<T>, index: nat := 0): (n: nat)
    requires x in xs
    requires index < |xs|
    requires x !in xs[..index]
    ensures n < |xs|
    decreases |xs| - index
  {
    if |xs| == 1 then
      assert xs[index] == x;
      index
    else if xs[index] == x then index
    else
      FindVal(x, xs, index + 1)
  }

}
