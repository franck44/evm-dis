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
include "../utils/EVMOpcodes.dfy"
include "../utils/State.dfy"

/**
  *  Provides EVM Instruction types.
  */
module Instructions {

  import opened Int
  import opened MiscTypes
  import opened EVMOpcodes
  import opened EVMConstants
  import opened State

  type ValidInstruction = i:Instruction |
      i.op.opcode == INVALID ||
      |i.arg| % 2 == 0 witness Instruction(SysOp("STOP", STOP), [], 0)

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
      *  Track position of an element on the stack.
      *  @param      pos     The position to track.
      *  @returns            The position 
      *
      *  @example    After a PUSH, the stack position k is k + 1 in the new stack.
      *              Hence the position k' in the new stack should be at k' - 1 in the source stack.
      *  @example    After a POP, the stack position k > 0 is k - 1 in the new stack. 
      *              Hence the position k' in the new stack should be at k' + 1 in the source stack.
      *  
      */
    function StackPosBackWardTracker(pos': nat := 0): Either<seq<char>, nat>
      requires this.op.IsValid()
    {
      match this.op
      case ArithOp(_, _, _, _, pushes, pops)      =>
        //  if pos' == 0, the value depends on two stack elements and
        //  we don't track it.
        //  Note that because this.op must be valid, pos' + pops - pushes is >= 0!
        if pos' >= 1 then Right(pos' + pops - pushes)
        else Left("More than one predecessor. Arithmetic operator with target 0")

      case CompOp(_, _, _, _, pushes, pops)       =>
        //  Same as Arithmetic operator, except some have only one operand.
        if pos' >= 1 then
          //  Note that because this.op must be valid, pos' + pops - pushes is >= 0!
          Right(pos' + pops - pushes)
        else Left("More than one predecessor. Comparison operator with target 0")

      case BitwiseOp(_, _, _, _, _, _)    => Left("Not implemented")
      case KeccakOp(_, _, _, _, _, _)     => Left("Not implemented")
      case EnvOp(_, _, _, _, _, _)        => Left("Not implemented")
      case MemOp(_, _, _, _, _, _)        => Left("Not implemented")
      case StorageOp(_, _, _, _, _, _)    => Left("Not implemented")

      case JumpOp(_, opcode, _, _, _, _)  =>
        if opcode == JUMPDEST then
          Right(pos')
        else if JUMP <= opcode <= JUMPI then
          //    If JUMP +1, if JUMPI + 2
          var k := opcode - JUMP + 1;
          Right(pos' + k as nat)
        else
          Left("Not implemented")

      case RunOp(_, _, _, _, _, _)        => Left("Not implemented")

      case StackOp(_, opcode, _, _, _, _) =>
        if PUSH0 <= opcode <= PUSH32 then
          //  PUSH k
          if pos' == 0 then Left(this.arg) else Right(pos' - 1)
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


      case LogOp(_, _, _, _, _, _) => Left("Not implemented")
      case SysOp(_, _, _, _, _, _) => Left("Not implemented")
    }

    /**
      * Compute the next abstract state. The condition resolves non-determinism when needed,
      * e.g. for JUMPs. Otherwise it shoudk be false as there is only one branch.
      * 
      * @param  s       The source state.
      * @param  cond    The branch to take for conditional instructions, false for others.
      */
    function NextState(s: ValidState, cond: bool := false): AState
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
        else if opcode == JUMP && s.Size() >= 1 && !cond then
          match s.Peek(0)
          case Value(v) => s.Pop().Goto(v as nat)
          case Random() => Error()
        else if opcode == JUMPI && s.Size() >= 2 then
          match s.Peek(0)
          case Value(v) =>
            if cond then s.PopN(2).Goto(v as nat)
            else s.PopN(2).Skip(1)
          case Random() => Error()
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
          s.Push(Value(0)).Skip(1)
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
  }
}
