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

include "../utils/EVMOpcodes.dfy"
include "../utils/MiscTypes.dfy"
include "../utils/Instructions.dfy"
include "../utils/LinSegments.dfy"

/**
  *  Provides ability to split the code into sections, ending in a JUMP/RETURN/REVERT 
  */
module Splitter {

  import opened EVMOpcodes
  import opened MiscTypes
  import opened Instructions
  import opened EVMConstants
  import opened LinSegments

  /**
    *   Determine the type of the segment according to the last instruction.
    *   @returns    A segment with instructions xs + [lastIns].
    */
  function BuildSeg(xs: seq<ValidInstruction>, lastInst: ValidInstruction): ValidLinSeg
    requires forall i:: 1 <= i <= |xs| ==> (xs + [lastInst])[i].op.opcode != JUMPDEST
  {
    match lastInst.op.opcode
    case JUMP   =>
      JUMPSeg(xs, lastInst, DeltaOperandsHelper(xs + [lastInst]))
    case JUMPI  =>
      JUMPISeg(xs, lastInst, DeltaOperandsHelper(xs + [lastInst]))
    case RETURN =>
      RETURNSeg(xs, lastInst, DeltaOperandsHelper(xs))
    case REVERT =>
      STOPSeg(xs, lastInst, DeltaOperandsHelper(xs))
    case STOP   =>
      STOPSeg(xs, lastInst, DeltaOperandsHelper(xs))
    case INVALID   =>
      INVALIDSeg(xs, lastInst, DeltaOperandsHelper(xs))
    case _ =>
      //  Continuation segment
      CONTSeg(xs, lastInst, DeltaOperandsHelper(xs + [lastInst]))
  }

  /**  
    *   Split the sequence of instructions according to boundaries jumpdests/jumps.
    *   @param  xs          The sequence of instructions to split.
    *   @param  curseq      The current sequence of instructions being built.
    *   @param  collected   The list of segments collected so far.
    *   @returns            A list of segments.
    *
    *   @note   Build a LinSeg for each section ending with a Jump or 
    *           until end of sequence.
    */
  function {:opaque} SplitUpToTerminal(xs: seq<ValidInstruction>, curseq: seq<ValidInstruction> := [], collected: seq<ValidLinSeg> := []): (r: seq<ValidLinSeg>)
    requires forall i, i':: 0 <= i < i' < |xs| ==> xs[i].address < xs[i'].address
    requires forall i:: 1 <= i < |curseq| ==> curseq[i].op.opcode != JUMPDEST
    requires forall i:: 0 <= i < |collected| ==> |collected[i].Ins()| > 0
    requires forall i, k:: 0 <= i < |curseq| && 0 <= k < |xs| ==> xs[k].address > curseq[i].address
    requires forall i, k:: 0 <= i < |collected| && 0 <= k < |xs| ==> xs[k].address > collected[i].StartAddress()
    requires forall i, k:: 0 <= i < |curseq| && 0 <= k < |collected| ==> collected[k].StartAddress() < curseq[i].address
    requires forall i, i':: 0 <= i < i' < |collected| ==> collected[i].StartAddress() < collected[i'].StartAddress()

    ensures forall i:: 0 <= i < |r| ==> |r[i].Ins()| > 0
    ensures forall i, i':: 0 <= i < i' < |r| ==> r[i].StartAddress() < r[i'].StartAddress()
  {
    if |xs| == 0 then
      //  No more instructions
      if |curseq| == 0 then collected
      else
        // Build the last segment from curseq
        var newSeg := BuildSeg(curseq[..|curseq| - 1], curseq[|curseq| - 1]);
        collected + [newSeg]
    //  if xs[0] is a jumpdest then start a new seg.
    else if xs[0].op.opcode == JUMPDEST then
      // Check if curseq is empty or not
      if |curseq| == 0 then
        SplitUpToTerminal(xs[1..], [xs[0]], collected)
      else
        //  If curseq not empty, build a segemtnwith curseq and add it to collected
        var newSeg := BuildSeg(curseq[..|curseq| - 1], curseq[|curseq| - 1]);
        SplitUpToTerminal(xs[1..], [xs[0]], collected + [newSeg])
    else if xs[0].IsTerminal() then
      //    x[0] is a terminal instruction
      assert xs[0].op.opcode != JUMPDEST;
      //    Build a segment and start with empty curseq
      var newSeg := BuildSeg(curseq, xs[0]);
      SplitUpToTerminal(xs[1..], [], collected + [newSeg])
    else
      //  x[0] is not a terminal instruction
      assert !xs[0].IsTerminal() && xs[0].op.opcode != JUMPDEST;
      SplitUpToTerminal(xs[1..], curseq + [xs[0]], collected)
  }

  /**
    *   The global effect of xs on the stack size.
    */
  function DeltaOperandsHelper(xs: seq<Instruction>, current: int := 0): int
    decreases |xs|
  {
    if |xs| == 0 then current
    else
      var e := current + (xs[0].op.pushes - xs[0].op.pops);
      DeltaOperandsHelper(xs[1..], e)
  }

  /**
    *   The global effect of xs on the capacity.
    */
  ghost function DeltaCapacityHelper(xs: seq<Instruction>, current: int := 0): int
    decreases |xs|
  {
    if |xs| == 0 then current
    else
      var e := current + (xs[0].op.pops - xs[0].op.pushes);
      DeltaCapacityHelper(xs[1..], e)
  }

  //  Helper lemmas

  /**
    *   Increase or decrease in the stack size is the opposite 
    *   of increase or decrease in capacity.
    */
  lemma PreserveDelta(xs: seq<Instruction>)
    ensures DeltaCapacityHelper(xs, 0) == -DeltaOperandsHelper(xs, 0)
  {
    if |xs| > 0 {
      var e := 0 + (xs[0].op.pushes - xs[0].op.pops);
      var e' := 0 + (xs[0].op.pops - xs[0].op.pushes);
      calc == {
        DeltaCapacityHelper(xs, 0);
        DeltaCapacityHelper(xs[1..], e');
        { DistributeDelta(xs[1..], xs[0].op.pops - xs[0].op.pushes); }
        (xs[0].op.pops - xs[0].op.pushes) + DeltaCapacityHelper(xs[1..], 0);
        { PreserveDelta(xs[1..]); }
        (xs[0].op.pops - xs[0].op.pushes) + (-DeltaOperandsHelper(xs[1..], 0));
        (xs[0].op.pops - xs[0].op.pushes - DeltaOperandsHelper(xs[1..], 0));
        { DistributeDelta(xs[1..], xs[0].op.pushes - xs[0].op.pops);}
        -DeltaOperandsHelper(xs[1..], e);
        -DeltaOperandsHelper(xs, 0);
      }
    }
  }

  lemma DistributeDelta(xs: seq<Instruction>, v1: int)
    ensures DeltaCapacityHelper(xs, v1) == v1 + DeltaCapacityHelper(xs, 0)
    ensures DeltaOperandsHelper(xs, v1) == v1 + DeltaOperandsHelper(xs, 0)
  {
    //  Thanks Dafny
  }


}

