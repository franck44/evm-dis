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
    case JUMP   => JUMPSeg(xs, lastInst)
    case JUMPI  => JUMPISeg(xs, lastInst)
    case RETURN => RETURNSeg(xs, lastInst)
    case STOP   => STOPSeg(xs, lastInst)
    case _      => UNKNOWNSeg(xs, lastInst)
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

}

