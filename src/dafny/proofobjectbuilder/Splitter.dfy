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
      JUMPSeg(xs, lastInst)
    case JUMPI  =>
      JUMPISeg(xs, lastInst)
    case RETURN =>
      RETURNSeg(xs, lastInst)
    case REVERT =>
      STOPSeg(xs, lastInst)
    case STOP   =>
      STOPSeg(xs, lastInst)
    case INVALID   =>
      INVALIDSeg(xs, lastInst)
    case _ =>
      //  Continuation segment
      CONTSeg(xs, lastInst)
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
  function {:opaque} SplitUpToTerminal(xs: seq<ValidInstruction>, maxSegSize: Option<nat> := None, curseq: seq<ValidInstruction> := [], collected: seq<ValidLinSeg> := []): (r: seq<ValidLinSeg>)
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
        SplitUpToTerminal(xs[1..], maxSegSize, [xs[0]], collected)
      else
        //  If curseq not empty, build a segment with curseq and add it to collected
        var newSeg := BuildSeg(curseq[..|curseq| - 1], curseq[|curseq| - 1]);
        SplitUpToTerminal(xs[1..], maxSegSize, [xs[0]], collected + [newSeg])
    else if xs[0].IsTerminal() then
      //    x[0] is a terminal instruction
      assert xs[0].op.opcode != JUMPDEST;
      //    Build a segment and start with empty curseq
      var newSeg := BuildSeg(curseq, xs[0]);
      SplitUpToTerminal(xs[1..], maxSegSize , [], collected + [newSeg])
    else if maxSegSize.Some? && |curseq| >= maxSegSize.v then
      var newSeg := BuildSeg(curseq, xs[0]);
      SplitUpToTerminal(xs[1..], maxSegSize, [], collected + [newSeg])
    else
      //  x[0] is not a terminal instruction
      assert !xs[0].IsTerminal() && xs[0].op.opcode != JUMPDEST;
      SplitUpToTerminal(xs[1..], maxSegSize, curseq + [xs[0]], collected)
  }

}

