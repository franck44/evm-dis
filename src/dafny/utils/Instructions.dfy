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
        assert pushes == 1;
        assert pops == 2 ;
        if pos' >= 1 then
          assert pos' + pops - pushes == pos' + 1;
          //  We return Right(pos' + pops - pushes)
          Right(pos' + 1)
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
            else if pos' == k then 0
            else pos'
          )
        else // Thanks to the Valid constraint on the opcode type, this can only be POP.
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
        if opcode == JUMPDEST then
          if !cond then s.Skip(1) else Error("Cannot execute JUMPDEST/exit true")
        else if opcode == JUMP then
          if s.Size() >= 1 && cond then
            match s.Peek(0)
            case Value(v) => s.Pop().Goto(v as nat)
            case Random(_) => Error()
          else
            Error("Cannot execute JUMP/exit false or stack underflow")
        else if opcode == JUMPI then
          if s.Size() >= 2 then
            match s.Peek(0)
            case Value(v) =>
              if cond then s.PopN(2).Goto(v as nat)
              else s.PopN(2).Skip(1)
            case Random(_) => Error()
          else
            Error("Cannot execute JUMPI/strack underflow")
        else
          assert RJUMP <= opcode <= RJUMPV;
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
      * Weakest pre of a stack (post) Cond.
      *
      * This computation does not need to know the branch taken at a JUMPI.
      * Indeed, we compute backward so the tgt PC is determined.
      * The effect on the stack is the same whatever the branching.
      */
    function WPre(c: ValidCond): ValidCond
      requires this.IsValid()
      requires c.StCond?
    {
      match this.op
      case ArithOp(_, _, _, _, pushes, pops)      =>
        assert pushes == 1;
        assert pops == 2 ;
        //  if one of the trackedPos is 0, return False, otherwise, pos' + 1 for each trackedPos
        if 0 in c.TrackedPos() then StFalse()
        else
          var shiftByOne := Map(c.TrackedPos(), pos =>  pos + 1);
          StCond(shiftByOne, c.TrackedVals())

      case CompOp(_, _, _, _, pushes, pops)      =>
        //  if one of the trackedPos is 0, return False, otherwise, pos' + pops - pushes for each trackedPos
        if 0 in c.TrackedPos() then StFalse()
        else
          var shiftBy := Map(c.TrackedPos(), pos =>  pos + pops - pushes);
          StCond(shiftBy, c.TrackedVals())

      case JumpOp(_, opcode, _, _, _, _)  =>
        if opcode == JUMPDEST then c
        else if JUMP <= opcode <= JUMPI then
          //    If JUMP +1, if JUMPI + 2
          var k := opcode - JUMP + 1;
          var shiftBy := Map(c.TrackedPos(), pos =>  pos + k as nat);
          StCond(shiftBy, c.TrackedVals())
        else  // RJUMPs not implemented
          StFalse()

      case StackOp(_, opcode, _, _, _, _) =>
        //  Pushes may resolve some tracked positions
        if PUSH0 <= opcode <= PUSH32 then
          //  PUSH k
          match Find(c.TrackedPos(), 0)
          case None =>
            //  Map to old position - 1
            var shiftByMinusOne := Map(c.TrackedPos(), (pos: nat) =>  pos - 1);
            StCond(shiftByMinusOne, c.TrackedVals())
          case Some(i) =>
            var argVal := Hex.HexToU256(seq(64 - |arg|, _ => '0') + arg);
            assert argVal.Some?;
            //  Check that the value pushed is the same as the trackedValue
            // assert
            if c.TrackedValAt(i) == argVal.Extract() then
              //  We can filter out position 0 as it is resolved
              var filtered := c.TrackedPos()[..i] + c.TrackedPos()[i + 1..];
              assert forall k:: 0 <= k < |c.TrackedPos()[..i]| ==> c.TrackedPos()[k] != c.TrackedPosAt(i);
              assert forall k {:trigger  filtered[k]}:: 0 <= k < |c.TrackedPos()[i + 1..]| ==> c.TrackedPos()[i + 1 + k] != c.TrackedPosAt(i);
              assert c.TrackedPosAt(i) == 0;
              assert forall k:: 0 <= k < |filtered| ==> filtered[k] != c.TrackedPosAt(i);
              assert forall k:: 0 <= k < |filtered| ==> filtered[k] != 0;
              if |filtered| == 0 then StTrue()
              else
                //  Map to old position - 1
                var shiftByMinusOne := Map(filtered, (pos: nat) =>  pos - 1);
                StCond(shiftByMinusOne, c.TrackedVals()[..i] + c.TrackedVals()[i + 1..])
            else StFalse()

        else if DUP1 <= opcode <= DUP16 then
          //    DUP1 to DUP16
          //   Shift positions as follow: if pos' == 0 then (opcode - DUP1) as nat  else pos' - 1)
          match Find(c.TrackedPos(), 0)
          case None =>
            //  0 is not tracked so the update cannot create a conflict with two same positions
            assert forall k:: 0 <= k < |c.TrackedPos()| ==> c.TrackedPos()[k] != 0;
            var shiftByMinusOneButZero :=
              Map(c.TrackedPos(), (pos:nat) =>  pos - 1);
            assert forall k, k':: 0 <= k < k'< |shiftByMinusOneButZero| ==> shiftByMinusOneButZero[k] != shiftByMinusOneButZero[k'];
            StCond(shiftByMinusOneButZero, c.TrackedVals())
          case Some(index0) =>
            //  0 is tracked. If there is another position index such that the position tracked
            //  is (opcode - DUP1) as nat + 1 there is a conflict.
            match Find(c.TrackedPos(), (opcode - DUP1) as nat + 1)
            case Some(index) =>
              //  There is a collision in tracked positions on the Wpre
              //  example: stack [x0, x1, x2] + DUP2 [x2, x0, x1, x2]
              //  trackedPos = [2, 2] <- DUP2 + trackedPos = [0, 3]
              if c.TrackedValAt(index0) == c.TrackedValAt(index) then
                //  no inconsistency. Collapse the two positions into one
                var filtered := c.TrackedPos()[..index0] + c.TrackedPos()[index0 + 1..];
                assert forall k:: 0 <= k < |filtered| ==> filtered[k] != 0;
                var shiftByMinusOne := Map(filtered, (pos: nat) =>  pos - 1);
                assert forall k, k':: 0 <= k < k' < |shiftByMinusOne| ==> shiftByMinusOne[k] != shiftByMinusOne[k'];
                StCond(shiftByMinusOne, c.TrackedVals()[..index0] + c.TrackedVals()[index0 + 1..])
              else
                //  Inconsistency.
                StFalse()
            case None =>
              //  No collision
              assert Find(c.TrackedPos(), (opcode - DUP1) as nat + 1)  == None;
              assert forall k:: 0 <= k < |c.TrackedPos()| ==> c.TrackedPosAt(k) != (opcode - DUP1) as nat + 1;
              var shiftByMinusOneButZero :=
                Map(c.TrackedPos(), pos =>  if pos == 0 then (opcode - DUP1) as nat else  pos - 1);
              assert forall k, k':: 0 <= k < k'< |shiftByMinusOneButZero| ==> shiftByMinusOneButZero[k] != shiftByMinusOneButZero[k'];
              StCond(shiftByMinusOneButZero, c.TrackedVals())

        else if SWAP1 <= opcode <= SWAP16 then
          // SWAP1 to SWAP16
          // compute index of element to be swapped with top of stack
          var k: nat  := (opcode - SWAP1) as nat + 1;
          //    elements at index k and 0
          var swapZeroAndk :=
            Map(c.TrackedPos(), pos =>  if pos == 0 then k as nat else if pos == k then 0 else  pos);
          StCond(swapZeroAndk, c.TrackedVals())
        else // Thanks to the Valid constraint on the opcode type, this can only be POP.
          assert opcode == POP;
          //    Shift the constraints by one
          var shiftByOne := Map(c.TrackedPos(), i =>  i + 1);
          StCond(shiftByOne, c.TrackedVals())

      case _ => c

    }

    /**
      * Weakest pre of a stack (post) Cond.
      *
      * @note   If the condition is trivila true or false it is back propagated.
      *         Otherwise, if a position p must have value v, several cases may arise:
      *         1. p is resolved by the instruction. 
      *         2. p is not resolved and depends on a single position p'.
      *         If 1. is true it must be the case that the resolver v' is the same as v. Otherwise
      *         there is a mismatch between the request and the resolution. 
      *         Either way, the result for this position is v == v' (true or false).
      *         If 2. is true, the position p is not resolved by the instruction and back propagated.
      *         The result is the position p' that should be tracked before the instruction to make sure
      *         we know p after the instruction. This is a StackElem and maybe Random(), in that case
      *         we cannot track p and this is resolved in StFalse.
      */
    //     function Wpre2(c: ValidCond): ValidCond
    //       requires this.IsValid()
    //     {
    //       if c.StTrue? || c.StFalse? then
    //         c
    //       else
    //         assert c.StCond?;
    //         //    Track each position in c.trackedPos
    //         var x := seq(c.Size(), i requires 0 <= i < c.Size() => StackPosBackWardTracker(c.TrackedPosAt(i)));
    //         //  Each value in x is of the form: Left(value) or Left(random()) or Right(value).
    //         //  Right(p) means tracked by stack position p. Left(random()) means unknown,
    //         //  Left(value(v)) resolved by value v.
    //         //
    //         //  example 1
    //         //  pos= [ 12,             5,        ,       3       ,      0,               6]
    //         //  x = [Left_0(0x10), Left_1(random), Right_2(2),    Left_3(random),    Right_4(5)]
    //         //       resolved       havoced       replaced by 2     havoced        replaced by 5
    //         //  In such a case we cannot track some positions (1, 3) and the weakest pre condition is StFalse.

    //         //  example 2
    //         //  pos [ 1,              3,           ,    2   ]
    //         //  x = [Left_0(0x10), Right_1(2),     Right_2(5)]
    //         //       resolved    replaced by 2  replaced by 5
    //         //  In such a case we have resolved pos 0 (peek(1)), and have to track Peek(2) and Peek(5) instead
    //         //  of Peek(3) and Peek(2). If 0x10 is the same as StackvaluesAt(0) this is good and this index
    //         //  does not need to be tracked, otherwise there is mismatch and the pre condtiion is StFalse.

    //         //  example 3
    //         //  pos [ 1 ]
    //         //  x = [Left_0(0x10)]
    //         //       resolved
    //         //  In such a case we have resolved pos 0 (peek(1)), and the pre cond is StTrue.

    //         //  Compute the resolution map for each position. Equivalent to the table pos, x above.
    //         // var mappedPos: seq<(nat, Either<StackElem, nat>)> := Zip(c.TrackedPos(), x);
    //         var existsRandom := Exists(x, (x: Either<StackElem, nat>) => x.Left? && x.Left().Random?);
    //         if existsRandom then
    //           StFalse()
    //         else
    //           assert !existsRandom;
    //           //    If we are here then each Left in x is a Left(Value())
    //           assert forall k:: k in x ==> (k.Left? ==> k.Left().Value?);
    //           var mappedValues: seq<(Either<StackElem, nat>, u256)> := Zip(x, c.TrackedVals());
    //           //  now filter the Left(Value())
    //           var leftValues : seq<(Either<StackElem, nat>, u256)> :=
    //             Filter(mappedValues, (x: (Either<StackElem, nat>, u256)) => x.0.Left?);
    //           assert forall k:: k in leftValues ==> k.0.Left? && k.0.Left().Value?;
    //           //    Now map the first component to the extracted value
    //           var r := seq(|leftValues|,
    //                    i requires 0 <= i < |leftValues| => (leftValues[i].0.l.Extract(), leftValues[i].1));
    //           //  r should be of the form (x0, x0)(x1, x1) etc
    //           if Exists(r, (x: (u256, u256)) => x.0 != x.1) then StFalse()
    //           else
    //             //  every element in x is either a Right(k), or a Left(Value(k)) with k matching the
    //             //  required position at the end.
    //             //  We just have to propagate the positions that have a Right(k)
    //             var rightValues : seq<(Either<StackElem, nat>, u256)> :=
    //               Filter(mappedValues, (x: (Either<StackElem, nat>, u256)) => x.0.Right?);
    //             //  Now UnZip and mat the right values to StackPositions
    //             var (tPos, tVals) := UnZip(rightValues);
    //             var rtPos := seq(|tPos|, i requires 0 <= i < |tPos| => tPos[i].Right());
    //             StCond(rtPos, tVals)

    //     }
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
