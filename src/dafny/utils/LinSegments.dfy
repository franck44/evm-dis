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
      && (forall i:: 1 <= i < |Ins()| ==> Ins()[i].op.opcode != JUMPDEST)
      && match this
         case JUMPSeg(_, _ , _) => lastIns.op.opcode == JUMP
         case JUMPISeg(_, _ , _) => lastIns.op.opcode == JUMPI
         case RETURNSeg(_, _ , _) => lastIns.op.opcode == RETURN
         case STOPSeg(_, _ , _) => lastIns.op.opcode == STOP || lastIns.op.opcode == REVERT
         case CONTSeg(_, _, _) => lastIns.op.opcode != INVALID && lastIns.op.opcode != JUMPI
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

    /** The size of this segment, in bytes. */
    function Size(xi: seq<ValidInstruction> := Ins()): nat {
      if |xi| == 0 then 0
      else xi[0].Size() + Size(xi[1..])
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
    ghost function CollectAllJumpDest(rest: seq<Instruction>): seq<nat>
    {
      if |rest| == 0 then []
      else
      if rest[0].op.opcode == JUMPDEST then
        [rest[0].address] + CollectAllJumpDest(rest[1..])
      else
        CollectAllJumpDest(rest[1..])
    }

    /**
      *  In a valid segment, a JUMPDEST can only be the first instruction.
      *  As per lemma xxx, so we can optimise the collection of JUMPDEST.
      * Moreover there is ta ost one JUMPDEST in a valid segment.
      */
    function CollectJumpDest(): (r: seq<nat>)
      requires this.IsValid()
      ensures |r| <= 1
    {
      if Ins()[0].op.opcode == JUMPDEST then [Ins()[0].address]
      else []
    }

    /**
      *  In a valid segment, a JUMPDEST can only be the first instruction.
      * As a result CollectJumpDest is the same as CollectAllJumpDest.
      */
    lemma CollectOnlyFirst()
      requires this.IsValid()
      ensures CollectJumpDest() == CollectAllJumpDest(Ins())
    {
      CollectIsEmpty(Ins()[1..]);
    }

    /**
      * In a segment with no JUMPDEST, CollectAllJumpDest is empty.
      */
    lemma CollectIsEmpty(x: seq<Instruction>)
      requires this.IsValid()
      requires forall i:: 0 <= i < |x| ==> x[i].op.opcode != JUMPDEST
      ensures CollectAllJumpDest(x) == []
    {   //  Thanks Dafny
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
    function Run(s: ValidState, exit: nat, jumpDests: seq<nat>): AState
      requires this.IsValid()
      requires exit == 0 || (this.JUMPISeg? && exit == 1)
    {
      //  Run the instructions with exit false, except last
      var s' := RunIns(ins, s, jumpDests);
      if s'.Error? then s'
      else
        lastIns.NextState(s', jumpDests, exit)
    }

    /**
      * Compute the Wpre of c for a segment.
      * Overall the instructions.
      */
    function WPre(c: ValidCond): ValidCond
    {
      WPreIns(Ins(), c)
    }

    /**
      *  Number of successors of a segment.
      *  @note   JUMPI has 2, JUMP and mormal segments have 1, 
      *          and RETURN/STOP/INVALID have 0.
      */
    function NumberOfExits(): nat
      ensures NumberOfExits() <= 2
    {
      match this
      case JUMPISeg(_, _, _) => 2
      case JUMPSeg(_, _, _) => 1
      case CONTSeg(_, _, _)  => 1
      case _ => 0
    }

    /** Determine the condition such that the PC after the JUMP/JUMPI/true is k */
    function LeadsTo(k: nat, exit: nat): ValidCond
      requires this.IsValid()
      requires exit <= 1
      requires IsValidExit(exit)
      requires exit == 0 || (this.JUMPISeg? && exit == 1)
    {
      if k >= Int.TWO_256 then StFalse()
      else
        match this
        case JUMPSeg(_, _, _) =>
          if exit == 0 then
            var c := StCond([0], [k as Int.u256]);
            WPreIns(ins, c)
          else StFalse()
        case JUMPISeg(_, _, _)  =>
          if exit == 1 then
            var c := StCond([0], [k as Int.u256]);
            WPreIns(ins, c)
          else
          if k == this.StartAddressNextSeg() then StTrue() else StFalse()
        case CONTSeg(_, _, _) =>
          if exit == 0 && k == this.StartAddressNextSeg() then StTrue() else StFalse()
        case RETURNSeg(_, _, _) => StTrue()
        case STOPSeg(_, _, _) => StTrue()
        case INVALIDSeg(_, _, _) => StFalse()

    }

    /**
      * Whether k is valid exit for this.
      *
      * @param   k   The exit number.
      * @returns     Whether k is a valid exit for this.
      */
    predicate IsValidExit(k: nat)
      requires this.IsValid()
    {
      k == 0 || (this.JUMPISeg? && k == 1)
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
  function RunIns(xs: seq<ValidInstruction>, s: ValidState, jumpDests: seq<nat>): AState
  {
    if |xs| == 0 then s
    else
      var next := xs[0].NextState(s, jumpDests, 0);
      match next
      case Error(_) => next
      case EState(_, _) => RunIns(xs[1..], next, jumpDests)
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
  function WPreSeqSegs(path: seq<nat>, exits: seq<nat>, c: ValidCond, xs: seq<ValidLinSeg>, tgtPC: nat): ValidCond
    requires |path| == |exits|
    requires forall k:: k in path ==> k < |xs|
    requires forall i:: 0 <= i < |path| ==> path[i] < |xs|
    requires forall i:: 0 <= i < |exits| ==> exits[i] <= 1
    requires forall i:: 0 <= i < |exits| ==> exits[i] <= xs[path[i]].NumberOfExits() - 1
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
      foo(xs[path[|path| - 1]], exits[|exits| - 1]);
      var wp2 := xs[path[|path| - 1]].LeadsTo(tgtPC, exits[|exits| - 1]);
      //  compute Wpre on last segment and iterate on prefix
      WPreSeqSegs(path[..|path| - 1], exits[..|exits| - 1], w1.And(wp2), xs, xs[path[|path| - 1]].StartAddress())

  }

  lemma foo(s: ValidLinSeg, k: nat)
    requires s.IsValid()
    requires k <= s.NumberOfExits() - 1
    ensures s.IsValidExit(k)
  {
    //  Thanks Dafny for the proof
  }

  /**   Whether two segments are equivalent.
    *
    *   The equivalence is defined as same sequence of instructions
    *   for segments that are not JUMP/JUMPI.
    *   Equivalence of instructions meansa same instruction but at a different
    *   Address.
    *   For JUMP/JUMPI, equivalence is defined as same upto the JUMO/JUMPI.
    *   It also requires that the second last instruction is a PUSH 
    *   (pushing the address to jump to).
    *   @note   This  feature is experimental and aims at detecting segments
    *           of code that are duplicated.
    *   @note   We should make sure tha PC() is not used otherwise the semamtics
    *           is different.
    */
  predicate EquivSeg(s1: ValidLinSeg, s2: ValidLinSeg) {
    match s1
    case JUMPSeg(_, _, _) =>
      s2.JUMPSeg?
      && |s1.Ins()| == |s2.Ins()| >= 2
      && EVMConstants.PUSH1 <= s1.ins[|s1.ins| - 1].op.opcode == s2.ins[|s1.ins| - 1].op.opcode <= EVMConstants.PUSH32
      && (forall i:: 0 <= i < |s1.ins| - 1 ==> s1.ins[i].Equiv(s2.ins[i]))
    case JUMPISeg(_,_, _) =>
      s2.JUMPISeg?
      && |s1.Ins()| == |s2.Ins()| >= 2
      && EVMConstants.PUSH1 <= s1.ins[|s1.ins| - 1].op.opcode == s2.ins[|s1.ins| - 1].op.opcode <= EVMConstants.PUSH32
      && (forall i:: 0 <= i < |s1.ins| - 1 ==> s1.ins[i].Equiv(s2.ins[i]))
    case RETURNSeg(_, _, _) =>
      s2.RETURNSeg?
      && |s1.Ins()| == |s2.Ins()|
      && (forall i:: 0 <= i < |s1.Ins()|  ==> s1.Ins()[i].Equiv(s2.Ins()[i]))
    case STOPSeg(_, _, _) =>
      s2.STOPSeg?
      && |s1.Ins()| == |s2.Ins()|
      && (forall i:: 0 <= i < |s1.Ins()|  ==> s1.Ins()[i].Equiv(s2.Ins()[i]))
    case CONTSeg(_, _, _) =>
      s2.CONTSeg?
      && |s1.Ins()| == |s2.Ins()|
      && (forall i:: 0 <= i < |s1.Ins()|  ==> s1.Ins()[i].Equiv(s2.Ins()[i]))
    case INVALIDSeg(_, _, _) =>
      s2.INVALIDSeg?
      && |s1.Ins()| == |s2.Ins()|
      && (forall i:: 0 <= i < |s1.Ins()|  ==> s1.Ins()[i].Equiv(s2.Ins()[i]))
  }

}

