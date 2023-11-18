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
include "../utils/State.dfy"
include "../utils/WeakPre.dfy"

/**
  *  Provides ability to split the code into sections, ending in a JUMP/RETURN/REVERT 
  */
module LinSegments {

  import opened EVMOpcodes
  import opened MiscTypes
  import opened Instructions
  import opened EVMConstants
  import opened State
  import opened WeakPre

  /**
    *   A valid linear segment.
    */
  type ValidLinSeg = s: LinSeg | s.IsValid() witness CONTSeg([], Instruction(ArithOp("ADD" ,ADD)), 0)

  /**
    *   A linear segment of bytecode.
    *   @note   Linear segments are ... linear. They do not contain any
    *           jumps, returns, stops, except possibly the last instruction.
    *
    *   @example    JUMPDEST, POP, JUMP is a linear segment of type JUMP 
    *               as it ends with a JUMP instruction
    *   @example    JUMPDEST, SWAP2, SWAP1, DUP1, DUP4, LT, PUSH1 0, JUMPI is a linear 
    *               segment of type JUMPI.
    *   @example    JUMPDEST PUSH1 0x40 MSTORE PUSH1 0x20 PUSH1 0x40 RETURN is a linear 
    *               segment of type RETURN.
    */
  datatype LinSeg =
      JUMPSeg(ins: seq<ValidInstruction>, lastIns: ValidInstruction, netOpEffect: int )
    |   JUMPISeg(ins: seq<ValidInstruction>, lastIns: ValidInstruction, netOpEffect: int)
    |   RETURNSeg(ins: seq<ValidInstruction>, lastIns: ValidInstruction, netOpEffect: int)
    |   STOPSeg(ins: seq<ValidInstruction>, lastIns: ValidInstruction, netOpEffect: int)
    |   CONTSeg(ins: seq<ValidInstruction>, lastIns: ValidInstruction, netOpEffect: int)
    |   INVALIDSeg(ins: seq<ValidInstruction>, lastIns: ValidInstruction, netOpEffect: int)
  {
    /**
      * To be valid the type of the segment must agree with the type of
      * the lastInst.
      */
    predicate IsValid() {
      match this
      case JUMPSeg(_, _ , _) => lastIns.op.opcode == JUMP
      case JUMPISeg(_, _ , _) => lastIns.op.opcode == JUMPI
      case RETURNSeg(_, _ , _) => lastIns.op.opcode == RETURN
      case STOPSeg(_, _ , _) => lastIns.op.opcode == STOP || lastIns.op.opcode == REVERT
      case CONTSeg(_, _, _) => lastIns.op.opcode != INVALID
      case INVALIDSeg(_, _, _) => lastIns.op.opcode == INVALID
    }

    /**
      *  The instructions in this segment.
      */
    function Ins(): seq<Instruction>
      ensures |Ins()| >= 1
    {
      this.ins + [this.lastIns]
    }

    /** The start address is the address of the first instruction in the segment. */
    function StartAddress(): nat {
      Ins()[0].address
    }

    /**
      *  The net effect on the stack size.
      */
    function NetOpEffect() : int {
      netOpEffect
    }

    /**
      *  The net effect on the capacity of the stack.
      */
    function NetCapEffect() : int {
      -netOpEffect
    }

    /**
      *  The net effect on the stack size (synomym of NetOppEffect).
      */
    function StackEffect() : int {
      netOpEffect
    }

    /**
      *  The address just after the last instruction in this segment.
      */
    function StartAddressNextSeg(): nat
      requires |this.lastIns.arg| % 2 == 0
    {
      this.lastIns.address + 1 + |this.lastIns.arg|/2
    }

    /**
      * Collect the JUMPDEST in a sequence of instructions.
      */
    function {:tailrecursion true} CollectJumpDest(rest: seq<Instruction> := Ins()): seq<nat>
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
    function WeakestPreOperands(n: nat := 0): nat
    {
      WeakestPreOperandsHelper(this.Ins(), n)
    }

    /**
      *  The weakest precondition that guarantees that the segment can executed
      *  without a stack overflow, and such that at the end there are at least 
      *  n free slots on the stack.
      */
    function WeakestPreCapacity(n: nat := 0): nat
    {
      WeakestPreCapacityHelper(this.Ins(), n )
    }

    /**
      *  Execute the segment up to the end.
      */
    function Run(s: ValidState, exit: bool): AState
    {
      //  Run the instructions with exit false, except last
      var s' := RunIns(ins, s);
      if s'.Error? then s'
      else
        lastIns.NextState(s', exit)
    }

    /**
      * Compute the Wpre of c for a segment.
      * Overall the instructions.
      */
    function WPre(c: ValidCond): ValidCond
    {
      WPreIns(Ins(), c)
    }

    /** Whether a given segment has exit true or false. */
    predicate HasExit(b: bool)
    {
      match this
      case JUMPSeg(_, _, _) => b
      case JUMPISeg(_, _, _) => true
      case CONTSeg(_, _, _)  => !b
      case _ => false
    }

    /** Determine the condition such that the PC after the JUMP/JUMPI/true is k */
    function LeadsTo(k: nat): ValidCond
      requires this.IsValid()
      //   requires this.JUMPSeg? || this.JUMPISeg?
    {
      if k >= Int.TWO_256 then StFalse()
      else
        match this
        case JUMPSeg(_, _, _) =>
          var c := StCond([0], [k as Int.u256]);
          WPreIns(ins, c)
        case JUMPISeg(_, _, _)  =>
          var c := StCond([0], [k as Int.u256]);
          WPreIns(ins, c)
        case CONTSeg(_, _, _) =>
          if k == this.StartAddressNextSeg() then StTrue() else StFalse()
        case RETURNSeg(_, _, _) => StTrue()
        case STOPSeg(_, _, _) => StTrue()
        case INVALIDSeg(_, _, _) => StFalse()

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
  function WeakestPreOperandsHelper(xs: seq<Instruction>, postCond: nat := 0): nat
    decreases |xs|
  {
    if |xs| == 0 then postCond
    else
      var lastI := xs[|xs| - 1];
      var e := lastI.WeakestPreOperands(postCond);
      WeakestPreOperandsHelper(xs[..|xs| - 1], e)
  }

  /** 
    *   Compute the weakest pre condition on capacity to ensure that 
    *   the sequence xs can be executed without a stack overflow, and 
    *   at the end, there are at least postCond free slots on the stack.
    *
    *   @returns    The weakest pre cond as nat or None if the result is negative. 
    */
  function WeakestPreCapacityHelper(xs: seq<Instruction>, postCond: nat := 0): nat
    decreases |xs|
  {
    if |xs| == 0 then postCond
    else
      var lastI := xs[|xs| - 1];
      var e := lastI.WeakestPreCapacity(postCond);
      WeakestPreCapacityHelper(xs[..|xs| - 1], e)
  }

  /**
    *   Run a sequence of (valid) instructions with exit condition false (default).
    */
  function RunIns(xs: seq<ValidInstruction>, s: ValidState): AState
  {
    if |xs| == 0 then s
    else
      var next := xs[0].NextState(s);
      match next
      case Error(_) => next
      case EState(_, _) => RunIns(xs[1..], next)
  }

  /**
    *   WPre for a sequence of instructions.
    */
  function WPreIns(xs: seq<ValidInstruction>, c: ValidCond): ValidCond
  {
    if |xs| == 0 then c
    else if !c.StCond? then c // Wpre(_, false) = false and Wpre(_, true) = true
    else
      assert c.StCond?;
      var c1 := xs[|xs| - 1].WPre(c);
      WPreIns(xs[..|xs| - 1], c1)
  }

  /**
    *  Compute the WPre for a sequence of segments.
    *   @param  path    The sequence of segment numbers.
    *   @param  c       A (post) condition.
    *   @param  xs      A list of known segments.
    *   @returns        
    */
  function WPreSeqSegs(path: seq<nat>, c: ValidCond, xs: seq<ValidLinSeg>, tgtPC: nat): ValidCond
    requires forall k:: k in path ==> k < |xs|
    requires forall i:: 0 <= i < |path| ==> path[i] < |xs|
  {
    if |path| == 0 then
      //    path is empty or c is true of false so no need to back propagate further.
      c
    else
      assert |path| > 0;
      //    Compute Wpre for the condition for the segment
      var w1 := xs[path[|path| - 1]].WPre(c);
      //    Compute Wpre for feasibility of the segment, i.e. to ensure that
      //    the segment leads to to the next one.
      var wp2 := xs[path[|path| - 1]].LeadsTo(tgtPC);
      //  compute Wpre on last segment and iterate on prefix
      WPreSeqSegs(path[..|path| - 1], w1.And(wp2), xs, xs[path[|path| - 1]].StartAddress())

  }

  /**
    *   Retrieve num of segments that correspond to a PC if any.
    */
  function PCToSeg(xs: seq<ValidLinSeg>, pc: nat, rank: nat := 0): (r: Option<nat>)
    requires rank <= |xs|
    ensures r.Some? ==> r.v < |xs|
    ensures r.Some?  ==> xs[r.v].StartAddress() == pc
    decreases |xs| - rank
  {
    if rank == |xs| then None
    else if xs[rank].StartAddress() == pc then Some(rank)
    else PCToSeg(xs, pc, rank + 1)
  }


}

