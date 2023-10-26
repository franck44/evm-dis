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
/**
  *  Provides ability to split the code into sections, ending in a JUMP/RETURN/REVERT 
  */
module LinSegments {

  import opened EVMOpcodes
  import opened MiscTypes
  import opened Instructions
  import opened EVMConstants

  /**
    *   A linear seg,ent of bytecode.
    *   @note   Linear segments are ... linear. They do not contain any
    *           jumps, returns, stops, except possibly the last instruction.
    *
    *   @example    JUMPDEST, POP, JUMP is a lienar segment of type JUMP 
    *               as it ends with a JUMP instruction
    *   @example    JUMPDEST, SWAP2, SWAP1, DUP1, DUP4, LT, PUSH1 0, JUMPI is a linear 
    *               segment of type JUMPI.
    *   @example    JUMPDEST PUSH1 0x40 MSTORE PUSH1 0x20 PUSH1 0x40 RETURN is a linear 
    *               segment of type RETURN.
    */
  datatype LinSeg =
      JUMPSeg(ins: seq<Instruction>, lastIns: Instruction)
    |   JUMPISeg(ins: seq<Instruction>, lastIns: Instruction)
    |   RETURNSeg(ins: seq<Instruction>, lastIns: Instruction)
    |   STOPSeg(ins: seq<Instruction>, lastIns: Instruction)
    |   UNKNOWNSeg(ins: seq<Instruction>, lastIns: Instruction)
  {
    /**
      *  The instructions in a segment.
      */
    function Ins(): seq<Instruction> {
      this.ins + [this.lastIns]
    }

    function StackEffect(xs: seq<Instruction> := Ins()) : int {
        StackEffectHelper(xs)
    }

    //  LastIns cannot be a JUMPDEST
    function {:tailrecursion true} CollectJumpDest(rest: seq<Instruction> := ins): seq<nat>
    {
        if |rest| == 0 then []
        else 
            if rest[0].op.opcode == JUMPDEST then 
                [rest[0].address] + CollectJumpDest(rest[1..])
            else 
                CollectJumpDest(rest[1..])
    }
 

    /**
      *  The weakest precondition that guarantees that the segment can executed
      *  without a stack underflow, and such that at the end there are at least 
      *  n operands on the stack.
      */
    function WeakestPreOperands(n: nat): Option<nat>
    {
      WeakestPreOperandsHelper(this.Ins())
    }

    /**
      *  The weakest precondition that guarantees that the segment can executed
      *  without a stack overflow, and such that at the end there are at least 
      *  n free slots on the stack.
      */
    function WeakestPreCapacity(n: nat): Option<nat>
    {
      WeakestPreCapacityHelper(this.Ins())
    }

  }

  //    Helpers
    function {:tailrecursion true} StackEffectHelper(xs: seq<Instruction>): int {
        if |xs| == 0 then 0 
        else 
            xs[0].StackEffect() + StackEffectHelper(xs[1..])
    }


  /** 
    *   Compute the weakest pre condition on operands to ensure that 
    *   the sequence xs can be executed without a stack underflow, and 
    *   at the end, there are at least postCond operands on the stack.
    *
    *   @returns    The weakest pre cond as nat or None if the result is negative. 
    */
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

  /** 
    *   Compute the weakest pre condition on capacity to ensure that 
    *   the sequence xs can be executed without a stack overflow, and 
    *   at the end, there are at least postCond free slots on the stack.
    *
    *   @returns    The weakest pre cond as nat or None if the result is negative. 
    */
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

