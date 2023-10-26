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

/**
  *  Provides EVM Instruction types.
  */
module Instructions {

  import opened Int
  import opened MiscTypes
  import opened EVMOpcodes
  import opened EVMConstants

  /** Make sur op is a correctly constructed Opcode */
  type ValidOpcode = x: Opcode | x.IsValid() witness SysOp("STOP", STOP)

  /**
    * An instruction.
    * @param    op  The opcode of the instruction.
    * @param    arg The (possibly empty) arguments.
    *
    * @example      `POP`, 'ADD, etc are instructiopns with no parameters, 
    *               whereas `PUSH1` or `PUSH2` takes parameters.  
    */
  datatype Instruction = Instruction(op: ValidOpcode, arg: seq<char> := [], address: nat := 0)
  {
   
    function ToString(): string
    {
      var x: string := arg;
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
    {
      match this.op
      case ArithOp(_, _, _, _, _, _)      => Right(0)
      case CompOp(_, _, _, _, _, _)       => Right(0)
      case BitwiseOp(_, _, _, _, _, _)    => Right(0)
      case KeccakOp(_, _, _, _, _, _)     => Right(0)
      case EnvOp(_, _, _, _, _, _)        => Right(0)
      case MemOp(_, _, _, _, _, _)        => Right(0)
      case StorageOp(_, _, _, _, _, _)    => Right(0)
      case JumpOp(_, opcode, _, _, _, _)       =>
        if opcode == JUMPDEST then
          Right(pos')
        else
          Right(0)
      case RunOp(_, _, _, _, _, _)        => Right(0)
      case StackOp(_, opcode, _, _, _, _) =>
        if PUSH0 <= opcode <= PUSH32 then
          //  PUSH k
          if pos' == 0 then Left(this.arg) else Right(pos' - 1)
        else if DUP1 <= opcode <= DUP16 then
          //    DUP1 to DUP16
          Right(if pos' == 0 then (opcode - 0x80) as nat  else pos' - 1)
        else if SWAP1 <= opcode <= SWAP16 then
          // SWAP1 to SWAP16
          Right(0)
        else // Thanks to the Valid constraint on the opcode type, this can only be OP.
          assert opcode == POP;
          Right(pos' + 1)


      case LogOp(_, _, _, _, _, _) => Right(0)
      case SysOp(_, _, _, _, _, _) => Right(0)
    }
  }
}
