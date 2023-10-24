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

  datatype LinSeg = LinSeg(ins: seq<Instruction>)
  {
    function Ins(): seq<Instruction> {
      this.ins
    }
  }

  function SplitUpToTerminal(xs: seq<Instruction>, curseq: seq<Instruction> := [], collected: seq<LinSeg> := []): seq<LinSeg>
  {
    if |xs| == 0 then collected
    else
    //  if xs[0] is terminal then start a new seg, otherwise continue previous
    if xs[0].IsTerminal() then
      var newSeg := curseq + [xs[0]];
      SplitUpToTerminal(xs[1..], [], collected + [LinSeg(newSeg)])
    else
      SplitUpToTerminal(xs[1..], curseq + [xs[0]], collected)
  }

  function WeakestPreOperands(x: LinSeg, postCond: nat := 0): Option<nat> 
    decreases |x.ins|
  {
    if |x.Ins()| == 0 then Some(postCond)
    else 
        var lastI := x.Ins()[|x.Ins()| - 1];
        var e := lastI.WeakestPreOperands(postCond);
        if e >= 0 then 
            WeakestPreOperands(LinSeg(x.Ins()[..|x.Ins()| - 1]), e) 
        else
            None
  }

}

