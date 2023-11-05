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
include "./Hex.dfy"
include "../utils/EVMOpcodes.dfy"
include "../utils/StackElement.dfy"
include "../utils/State.dfy"
include "../utils/WeakPre.dfy"

/** 
  *  Provides EVM Instruction types.
  */
module Instructions {

  import opened Int
  import Hex
  import opened MiscTypes
  import opened EVMOpcodes
  import opened EVMConstants
  import opened StackElement
  import opened State
  import opened WeakPre

  type ValidInstruction = i:Instruction | i.IsValid()
    witness Instruction(SysOp("STOP", STOP), [], 0)

  /**
    * An instruction.
    * @param    op  The opcode of the instruction.
    * @param    arg The (possibly empty) number of arguments in BYTES.
    *
    * @example      `POP`, 'ADD, etc are instructions with no parameters, 
    *               whereas `PUSH1` or `PUSH2` takes parameters.  
    * @note         The numbers of arguments as Hex is arg/2.
    */
  datatype Instruction = Instruction(op: ValidOpcode, arg: seq<char> := [], address: nat := 0)
  {

    /** Whether an instruction has been built correctly. */
    predicate IsValid() {
      op.opcode == INVALID ||
      (
        && (PUSH0 <= op.opcode <= PUSH32 ==>
              |arg| == 2 * (op.opcode - PUSH0) as nat && (forall k:: 0 <= k < |arg| ==> Hex.IsHex(arg[k])))
        && (!(PUSH0 <= op.opcode <= PUSH32) ==> |arg| == 0)
      )
    }

    /** Print as a string. */
    function ToString(): string
    {
      var x: string := arg;
      if op.opcode == INVALID then
        op.Name() + " " + x
      else
        op.Name() + (if |x| > 0 then " 0x" + x else "")
    }

    /**
      * Whether an instruction Opcode is terminal (branching).
      */
    predicate IsTerminal()
    {
      this.op.IsTerminal()
    }

    /**
      * Whether an instruction Opcode is terminal (branching).
      */
    predicate IsJumpDest()
    {
      this.op.IsJumpDest()
    }

    /**
      * The next effect on the stack size.
      */
    function StackEffect(): int
    {
      op.StackEffect()
    }

    /**
      *  Determine the minimum of operands needed before the
      *  instruction is executed to ensure that
      *  1. the instruction does not trigger a Stack underflow
      *  2. there are at least k operands on the stack after execuitng the instruction.
      *
      *  @example    POP: pushes 0, pops 1, minOperands 1
      *              k = 0 => Max(1, 0 -(-1)) = 1 
      *              k = 3 => Max(1, 3 - (- 1)) = 4
      *  @example    SWAP2 pushes 0, pops 0, minOperands 3
      *              k = 0 => r = 0 
      *              k = 1 => r = 1
      *              k => r = k!
      */
    function WeakestPreOperands(post: nat := 0): (r: nat)
    {
      op.WeakestPreOperands(post)
    }

    /**
      *  Determine the minimum of capacity needed before the
      *  instruction is executed to ensure that
      *  1. the instruction does not trigger a Stack overflow
      *  2. there are at least k free slots on the stack after executing the instruction.
      *
      *  @example    POP: pushes 0, pops 1, minCapacity = 0
      *              k = 0 => Max(0, 0 + (-1)) = 0
      *              k = 3 => Max(1, 3 + (- 1)) = 2
      *  @example    SWAP2 pushes 0, pops 0, minCapacity = 0
      *              k = 0 => Max(0, 0 + 0) = 0
      *              k = 1 => Max(0, 1 + 0) = 1
      */
    function WeakestPreCapacity(post: nat := 0): (r: nat)
    {
      op.WeakestPreCapacity(post)
    }

    /**
      * Track position of an element on the stack.
      * @param      pos     The position to track.
      * @returns            Either a value, Left(val), if the instruction "kills" 
      *                     the tracking (e.g. a PUSH for a pos == 0) or 
      *                     a stack position Right(p) otherwise.   
      *
      * @note               This is meant to track the pc after an instruction and the 
      *                     assumption is that pc values are pushes/popped/dupped/swapped
      *                     but not computed (e.g. via 'ADD' etc). As a result, the tracking
      *                     does not follow arithmetic etc.
      *
      *  @example    After a PUSH, the stack position k is k + 1 in the new stack.
      *              Hence the position k' in the new stack should be at k' - 1 in the source stack.
      *  @example    After a POP, the stack position k > 0 is k - 1 in the new stack. 
      *              Hence the position k' in the new stack should be at k' + 1 in the source stack.
      *  
      */
    function StackPosBackWardTracker(pos': nat := 0): Either<StackElem, nat>
      requires this.op.IsValid()
      requires this.IsValid()
    {
      match this.op
      case ArithOp(_, _, _, _, pushes, pops)      =>
        //  if pos' == 0, the value depends on two stack elements and
        //  we don't track it.
        //  Note that because this.op must be valid, pos' + pops - pushes is >= 0!
        if pos' >= 1 then Right(pos' + pops - pushes)
        else Left(Random("More than one predecessor. Arithmetic operator with target 0"))

      case CompOp(_, _, _, _, pushes, pops)       =>
        //  Same as Arithmetic operator, except some have only one operand.
        if pos' >= 1 then
          //  Note that because this.op must be valid, pos' + pops - pushes is >= 0!
          Right(pos' + pops - pushes)
        else Left(Random("More than one predecessor. Comparison operator with target 0"))

      case BitwiseOp(_, _, _, _, _, _)    => Left(Random("Not implemented"))
      case KeccakOp(_, _, _, _, _, _)     => Left(Random("Not implemented"))
      case EnvOp(_, _, _, _, _, _)        => Left(Random("Not implemented"))
      case MemOp(_, _, _, _, _, _)        => Left(Random("Not implemented"))
      case StorageOp(_, _, _, _, _, _)    => Left(Random("Not implemented"))

      case JumpOp(_, opcode, _, _, _, _)  =>
        if opcode == JUMPDEST then
          Right(pos')
        else if JUMP <= opcode <= JUMPI then
          //    If JUMP +1, if JUMPI + 2
          var k := opcode - JUMP + 1;
          Right(pos' + k as nat)
        else
          Left(Random("Not implemented"))

      case RunOp(_, _, _, _, _, _)        => Left(Random("Not implemented"))

      case StackOp(_, opcode, _, _, _, _) =>
        if PUSH0 <= opcode <= PUSH32 then
          //  PUSH k
          if pos' == 0 then Left(Value(GetArgValuePush(this.arg))) else Right(pos' - 1)
        else if DUP1 <= opcode <= DUP16 then
          //    DUP1 to DUP16
          Right(if pos' == 0 then (opcode - DUP1) as nat  else pos' - 1)
        else if SWAP1 <= opcode <= SWAP16 then
          // SWAP1 to SWAP16
          // compute index of element to be swapped with top of stack
          var k: nat  := (opcode - SWAP1) as nat + 1;
          Right(
            if pos' == 0 then k
            else if pos' == k + 1 then 0
            else pos'
          )
        else // Thanks to the Valid constraint on the opcode type, this can only be OP.
          assert opcode == POP;
          Right(pos' + 1)


      case LogOp(_, _, _, _, _, _) => Left(Random("Not implemented"))
      case SysOp(_, _, _, _, _, _) => Left(Random("Not implemented"))
    }

    /**
      * Compute the next abstract state. The condition resolves non-determinism when needed,
      * e.g. for JUMPs. Otherwise it shoudk be false as there is only one branch.
      * 
      * @param  s       The source state.
      * @param  cond    The branch to take for conditional instructions, false for others.
      * @note           The condition is true iff a JUMP/JUMPI is
      *                 taken. For instance, if the instruction is
      *                 JUMP only the true branch exists. If it is 
      *                 JUMPI true means branch to top of stack, 
      *                 and false, go to next instruction.
      */
    function NextState(s: ValidState, cond: bool := false): AState
      requires this.IsValid()
      requires this.op.IsValid()
    {
      match this.op
      case ArithOp(_, _, _, _, pushes, pops)      =>
        if s.Size() >= pops && !cond then
          assert pops == 2;
          assert pushes == 1;
          s.PopN(pops).Push(Random()).Skip(1)
        else Error("Stack underflow")

      case CompOp(_, _, _, _, pushes, pops)       =>
        //  Same as Arithmetic operator, except some have only one operand.
        if s.Size() >= pops && !cond then
          s.PopN(pops).Push(Random()).Skip(1)
        else Error("Stack underflow")

      case BitwiseOp(_, _, _, _, pushes, pops)    =>
        if s.Size() >= pops && !cond then
          s.PopN(pops).Push(Random()).Skip(1)
        else Error("Stack underflow")

      case KeccakOp(_, _, _, _, pushes, pops)     =>
        if s.Size() >= 2 && !cond then
          assert pushes == 1;
          assert pops == 2;
          s.PopN(2).Push(Random()).Skip(1)
        else Error("Stack underflow")

      case EnvOp(_, _, _, _, pushes, pops)        =>
        if !cond then
          assert pops == 0;
          assert pushes == 1;
          s.Push(Random()).Skip(1)
        else Error()

      case MemOp(_, _, _, _, pushes, pops)        =>
        if s.Size() >= pops && !cond then
          s.PopN(pops).Push(Random()).Skip(1)
        else Error()

      case StorageOp(_, _, _, _, pushes, pops)    =>
        if s.Size() >= pops && !cond then
          s.PopN(pops).Push(Random()).Skip(1)
        else Error()

      case JumpOp(_, opcode, _, _, pushes, pops)  =>
        assert pushes == 0;
        if opcode == JUMPDEST && !cond then
          s.Skip(1)
        else if opcode == JUMP && s.Size() >= 1 && cond then
          match s.Peek(0)
          case Value(v) => s.Pop().Goto(v as nat)
          case Random(_) => Error()
        else if opcode == JUMPI && s.Size() >= 2 then
          match s.Peek(0)
          case Value(v) =>
            if cond then s.PopN(2).Goto(v as nat)
            else s.PopN(2).Skip(1)
          case Random(_) => Error()
        else
          //    RJUMP not implemented
          Error("RJUMPs not implemented")

      case RunOp(_, _, _, _, pushes, pops)        =>
        if !cond then
          assert pops == 0;
          assert pushes == 1;
          s.Push(Random()).Skip(1)
        else Error()

      case StackOp(_, opcode, _, _, pushes, pops) =>
        if opcode == POP && s.Size() >= 1 && ! cond then
          assert pushes == 0 && pops == 1;
          s.Pop().Skip(1)
        else if PUSH0 <= opcode <= PUSH32 && !cond then
          assert pushes == 1;
          assert pops == 0;
          s.Push(Value(GetArgValuePush(arg))).Skip(1 + (opcode - PUSH0) as nat)
        else if DUP1 <= opcode <= DUP16 && s.Size() >= (opcode - DUP1) as nat + 1 && !cond then
          assert pushes == 1 && pops == 0;
          s.Dup((opcode - DUP1) as nat + 1).Skip(1)
        else if SWAP1 <= opcode <= SWAP16 && s.Size() > (opcode - SWAP1) as nat + 1 && !cond then
          assert pushes == pops == 0;
          s.Swap((opcode - SWAP1) as nat + 1).Skip(1)
        else
          Error()

      case LogOp(_, _, _, _, pushes, pops) =>
        assert pushes == 0;
        if s.Size() >= pops && !cond then
          s.PopN(pops).Skip(1)
        else Error()

      case SysOp(_, _, _, _, pushes, pops) =>
        if s.Size() >= pops && !cond then
          s.PopN(pops).PushNRandom(pushes).Skip(1)
        else Error()
    }

    /**
      *   Weakest pre of a Cond 
      */
    function Wpre(c: ValidCond): ValidCond
      requires this.IsValid()
    {
      //    Track each position in c.Pos
      var x := seq(c.Size(), i requires 0 <= i < c.Size() => StackPosBackWardTracker(c.Pos(i)));
      //    Each value is of the form: Left(value) or Left(random()) or Right(value)
      //    If a position in x is Right(), it does not need to be tracked as it resolved by the instruction.
      //    Example: let x map c.Pos to [Left_0, Left_1, Right_2, Left_3, Right_4]
      //    The new condition is defined by Pos' = [Left_0, Left_1, Left_3] and values [Pos(0), Pos(1), Pos(3)]
      var mappedPos: seq<(nat, Either<StackElem, nat>)> := Zip(c.positions, x);
      var rest: seq<(nat, Either<StackElem, nat>)> := Filter(mappedPos, (x: (nat, Either<StackElem, nat>)) => x.1.Left?);
      assert forall i:: 0 <= i < |rest| ==> rest[i].1.Left?;   
      var (r0, r1) := UnZip(rest);
      assert forall i:: 0 <= i < |r1| ==> r1[i] == rest[i].1; 
      Cond(r0, seq(|r1|, i requires 0 <= i < |r1| => r1[i].Left()))
    }
  }

    //  Helpers


  /**   Convert a seq of chars to a u256. */
  function GetArgValuePush(xc: seq<char>): u256
    requires |xc| <= 64
    requires forall k:: 0 <= k < |xc| ==> Hex.IsHex(xc[k])
  {
    var pad := seq(64 - |xc|, _ => '0');
    //  HexToU256 is a u256 (not None), so we can extract the value.
    assert Hex.HexToU256(pad + xc).Some?;
    Hex.HexToU256(pad + xc).Extract()
  }
}
