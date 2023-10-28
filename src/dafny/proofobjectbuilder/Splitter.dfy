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
  function BuildSeg(xs: seq<Instruction>, lastInst: Instruction): LinSeg
  {
    match lastInst.op.opcode
    case JUMP   =>
      JUMPSeg(xs, lastInst, DeltaOperandsHelper(xs + [lastInst]))
    case JUMPI  =>
      JUMPISeg(xs, lastInst, DeltaOperandsHelper(xs + [lastInst]))
    case RETURN =>
      RETURNSeg(xs, lastInst, DeltaOperandsHelper(xs))
    case STOP   =>
      STOPSeg(xs, lastInst, DeltaOperandsHelper(xs))
    case _      =>
      UNKNOWNSeg(xs, lastInst, DeltaOperandsHelper(xs + [lastInst]))
  }

  /**  
    *   Split the sequence of instructions according to jumps.
    *   @note   Build a LinSeg for each section ending with a Jump or until end of sequence.
    */
  function SplitUpToTerminal(xs: seq<Instruction>, curseq: seq<Instruction> := [], collected: seq<LinSeg> := []): seq<LinSeg>
  {
    if |xs| == 0 then collected
    else if |xs| == 1 then
      //  Last instruction in the code
      collected + [BuildSeg(curseq, xs[0])]
    //  if xs[0] is terminal then start a new seg, otherwise continue previous
    else if xs[0].IsTerminal() then
      var newSeg := curseq + [xs[0]];
      SplitUpToTerminal(xs[1..], [], collected + [BuildSeg(curseq, xs[0])])
    else
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

