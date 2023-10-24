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
  /**
    *  Provides ability to split the code into sections, ending in a JUMP/RETURN/REVERT 
    */
module Splitter {

  import opened EVMOpcodes
  import opened MiscTypes

  datatype LinSeg =
      JUMPSeg(ins: seq<Instruction>)
    |   JUMPISeg(ins: seq<Instruction>)
    |   RETURNSeg(ins: seq<Instruction>)
    |   STOPSeg(ins: seq<Instruction>)
    |   UNKNOWNSeg(ins: seq<Instruction>)
  {
    function Ins(): seq<Instruction> {
      this.ins
    }

    function WeakestPreOperands(n: nat): Option<nat>
    {
      WeakestPreOperandsHelper(this.ins)
    }

    function WeakestPreCapacity(n: nat): Option<nat>
    {
      WeakestPreCapacityHelper(this.ins)
    }
  }

  /**
    *  Determnine the type fo the segment from the last instruction
    */
  function BuildSeg(xs: seq<Instruction>, lastInst: Instruction): LinSeg
  {
    match lastInst.op.opcode
    case JUMP   => JUMPSeg(xs + [lastInst])
    case JUMPI  => JUMPISeg(xs + [lastInst])
    case RETURN => RETURNSeg(xs + [lastInst])
    case STOP   => STOPSeg(xs + [lastInst])
    case _      => UNKNOWNSeg(xs + [lastInst])
  }

  function SplitUpToTerminal(xs: seq<Instruction>, curseq: seq<Instruction> := [], collected: seq<LinSeg> := []): seq<LinSeg>
  {
    if |xs| == 0 then collected
    else
    //  if xs[0] is terminal then start a new seg, otherwise continue previous
    if xs[0].IsTerminal() then
      var newSeg := curseq + [xs[0]];
      SplitUpToTerminal(xs[1..], [], collected + [BuildSeg(curseq, xs[0])])
    else
      SplitUpToTerminal(xs[1..], curseq + [xs[0]], collected)
  }

  function WeakestPreOperandsHelper(xs: seq<Instruction>, postCond: nat := 0): Option<nat>
    decreases |xs|
  {
    if |xs| == 0 then Some(postCond)
    else
      var lastI := xs[|xs| - 1];
      var e := lastI.WeakestPreOperands(postCond);
      if e >= 0 then
        WeakestPreOperandsHelper(xs[..|xs| - 1], e)
      else
        None
  }

  function WeakestPreCapacityHelper(xs: seq<Instruction>, postCond: nat := 0): Option<nat>
    decreases |xs|
  {
    if |xs| == 0 then Some(postCond)
    else
      var lastI := xs[|xs| - 1];
      var e := lastI.WeakestPreCapacity(postCond);
      if e >= 0 then
        WeakestPreCapacityHelper(xs[..|xs| - 1], e)
      else
        None
  }

}

