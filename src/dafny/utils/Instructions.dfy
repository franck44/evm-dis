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
include "./EVMToolTips.dfy"
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
  import opened EVMToolTips

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
    /** Whether an instruction has been built correctly. 
      * If the Opcode is not INVALID then:
      * 1.  if it is a PUSH_k, the number of args is 2 * k and each arg is a valid Hex number
      * 2.  if it is bit a PUSH there are no arguments.
      */
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
      * Print node information to simple HTML form.
      */
    function ToHTML(): string
      requires this.IsValid()
    {
      var x: string := arg;
      var cols := Colours(this);
      var formattedAddress := seq(|Hex.NatToHex(address)| % 2, _ => '0') + Hex.NatToHex(address);

      var insText := if op.opcode == INVALID then
                       "<FONT color=\"" + cols.0 + "\">" + op.Name() + "</FONT>" + " " + x
                     else
                       "<FONT color=\"" + cols.0 + "\">" + op.Name() + "</FONT>"+ (if |x| > 0 then " 0x" + x else "");

      "0x" + formattedAddress + ":" + insText + " <BR ALIGN=\"LEFT\"/>\n"
    }

    /**   Print as an HTMNL Table 
      *   The port tag should be of the PORT="something" 
      */
    function ToHTMLTable(entryPortTag: string := "", exitPortTag: string := ""): string
      requires this.IsValid()
    {
      // cols.0 is pencolor and cols.1 is background
      var cols := Colours(this);
      var formattedAddress := seq(|Hex.NatToHex(address)| % 2, _ => '0') + Hex.NatToHex(address);
      var gasLine := "&#9981;";
      var oplineTD :=
        "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" "
        + entryPortTag + ">"
        + "0x"
        + formattedAddress
        + " </TD>\n"
        + "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: " + Gas(op.opcode) + " \" "
        + "target=\"_blank\" href=\""
        + gasRefLine
        + "\"" + ">" + gasLine + "</TD>"
        + "<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"" + cols.1 + "\" align=\"left\" cellpadding=\"3\" " + exitPortTag
        + " href=\"" + bytecodeRefLine + NatToString(ToolTip(op.opcode).1) + "\" target=\"_blank\" "
        + " tooltip=\"" + ToolTip(op.opcode).0 + "\" "
        +
        ">"
        + "<FONT color=\"" + cols.0 + "\">"+ op.Name() + "</FONT>"
        + "</TD>";
      var arglineTD := if |arg| > 0 then
                         "<TD width=\"1\" fixedsize=\"true\" align=\"left\">"
                         + "  0x" + arg
                         + "</TD>"
                       else "";
      var lineTR := "<TR>" + oplineTD + arglineTD + "</TR>";
      var itemTable :=
        "<TABLE  border=\"0\" cellpadding=\"0\" cellsborder=\"0\" CELLSPACING=\"1\">"
        + lineTR
        + "</TABLE>";
      itemTable
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
      * Whether an instruction Opcode is terminal (branching).
      */
    predicate IsJump()
    {
      this.op.IsJump()
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

      case BitwiseOp(_, _, _, _, pushes, pops)    =>
        //  Same as Arithmetic operator, except some have only one operand.
        if pos' >= 1 then
          //  Note that because this.op must be valid, pos' + pops - pushes is >= 0!
          Right(pos' + pops - pushes)
        else Left(Random("More than one predecessor. Bitwise operator with target 0"))

      case KeccakOp(_, _, _, _, pushes, pops)     =>
        assert pops == 2 && pushes == 1;
        //  Same as Arithmetic operator, except some have only one operand.
        if pos' >= 1 then
          //  Note that because this.op must be valid, pos' + pops - pushes is >= 0!
          Right(pos' + 1)
        else Left(Random("More than one predecessor. Keccak operator with target 0"))

      case EnvOp(_, _, _, _, pushes, pops)        =>
        if pushes == 1 && pops == 0 then
          if pos' == 0 then Left(Random("More than one predecessor. Env operator with target 0"))
          else
            Right(pos' - 1)
        else if pushes == 1 && pops == 1 then
          if pos' == 0 then Left(Random("More than one predecessor. Env operator with target 0"))
          else Right(pos')
        else
          assert pushes == 0 && 3 <= pops <= 4;
          Right(pos' + pops - pushes)

      case MemOp(_, _, _, _, pushes, pops)        =>
        if pushes == 0 then
          assert pops == 2;
          Right(pos' + 2)
        else
          assert pushes == pops == 1;
          if pos' == 0  then Left(Random("More than one predecessor. Mem operator with target 0"))
          else Right(pos')

      case StorageOp(_, _, _, _, pushes, pops)    =>
        if pushes == 0 then
          assert pops == 2;
          Right(pos' + 2)
        else
          assert pushes == pops == 1;
          if pos' == 0 then Left(Random("More than one predecessor. Storage operator with target 0"))
          else Right(pos')

      case JumpOp(_, opcode, _, _, _, _)  =>
        if opcode == JUMPDEST then
          Right(pos')
        else if JUMP <= opcode <= JUMPI then
          //    If JUMP +1, if JUMPI + 2
          var k := opcode - JUMP + 1;
          Right(pos' + k as nat)
        else
          assert JUMPDEST < opcode <= RJUMPV;
          Left(Random("Not implemented"))

      case RunOp(_, _, _, _, pushes, pops)        =>
        if pos' == 0 then Left(Random("More than one predecessor. Run operator with target 0"))
        else
          assert pushes == 1 && pops == 0;
          Right(pos' - 1)

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

      case LogOp(_, _, _, _, pushes, pops) =>
        assert pushes == 0 && 2 <= pops <= 6;
        Right(pos' + 2)

      case SysOp(_, _, _, _, pushes, pops) =>
        if pushes == 0 then
          Right(pos' + pops)
        else
          assert pushes == 1;
          if pos' == 0 then Left(Random("More than one predecessor. Sys operator with target 0"))
          else
            Right(pos' + pops)
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
          s.PopN(pops).PushNRandom(pushes).Skip(1)
        else Error("Stack underflow")

      case CompOp(_, _, _, _, pushes, pops)       =>
        //  Same as Arithmetic operator, except some have only one operand.
        if s.Size() >= pops && !cond then
          s.PopN(pops).PushNRandom(pushes).Skip(1)
        else Error("Stack underflow")

      case BitwiseOp(_, _, _, _, pushes, pops)    =>
        if s.Size() >= pops && !cond then
          s.PopN(pops).PushNRandom(pushes).Skip(1)
        else Error("Stack underflow")

      case KeccakOp(_, _, _, _, pushes, pops)     =>
        if s.Size() >= 2 && !cond then
          assert pushes == 1;
          assert pops == 2;
          s.PopN(2).Push(Random()).Skip(1)
        else Error("Stack underflow")

      case EnvOp(_, _, _, _, pushes, pops)        =>
        if s.Size() >= pops && !cond then
          s.PopN(pops).PushNRandom(pushes).Skip(1)
        else Error("EnvOp error")

      case MemOp(_, _, _, _, pushes, pops)        =>
        if s.Size() >= pops && !cond then
          s.PopN(pops).PushNRandom(pushes).Skip(1)
        else Error("MemOp error")

      case StorageOp(_, _, _, _, pushes, pops)    =>
        if s.Size() >= pops && !cond then
          s.PopN(pops).PushNRandom(pushes).Skip(1)
        else Error("Storage Op error")

      case JumpOp(_, opcode, _, _, pushes, pops)  =>
        assert pushes == 0;
        if opcode == JUMPDEST then
          if !cond then s.Skip(1) else Error("Cannot execute JUMPDEST/exit true")
        else if opcode == JUMP then
          if s.Size() >= 1 && cond then
            match s.Peek(0)
            case Value(v) => s.Pop().Goto(v as nat)
            case Random(_) => Error("Jump to Random() error")
          else
            Error("Cannot execute JUMP/exit false or stack underflow")
        else if opcode == JUMPI then
          if s.Size() >= 2 then
            match s.Peek(0)
            case Value(v) =>
              if cond then s.PopN(2).Goto(v as nat)
              else s.PopN(2).Skip(1)
            case Random(_) => Error("JumpI to Random() error")
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
        else Error("RunOp error")

      case StackOp(_, opcode, _, _, pushes, pops) =>
        if opcode == POP && s.Size() >= 1 && !cond then
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
          Error("Stack Op error")

      case LogOp(_, _, _, _, pushes, pops) =>
        assert pushes == 0;
        if s.Size() >= pops && !cond then
          s.PopN(pops).Skip(1)
        else Error("LogOp error")

      case SysOp(_, op, _, _, pushes, pops) =>
        if op == INVALID || op == STOP || op == REVERT then 
            Error("SysOp error")
        else if s.Size() >= pops && !cond then
          s.PopN(pops).PushNRandom(pushes).Skip(1)
        else Error("SysOp error")
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

      case BitwiseOp(_, _, _, _, pushes, pops)      =>
        //  if one of the trackedPos is 0, return False, otherwise, pos' + pops - pushes for each trackedPos
        if 0 in c.TrackedPos() then StFalse()
        else
          assert pops - pushes >= 0;
          var shiftBy := Map(c.TrackedPos(), pos =>  pos + pops - pushes);
          StCond(shiftBy, c.TrackedVals())

      case KeccakOp(_, _, _, _, pushes, pops)      =>
        //  if one of the trackedPos is 0, return False, otherwise, pos' + pops - pushes for each trackedPos
        assert pops == 2 && pushes == 1;
        if 0 in c.TrackedPos() then StFalse()
        else
          var shiftByOne := Map(c.TrackedPos(), pos =>  pos + 1);
          StCond(shiftByOne, c.TrackedVals())

      case EnvOp(_, _, _, _, pushes, pops)      =>
        //  EnvOp instructions may push and pop various number of elements
        if pushes == 1 && pops == 0 then
          if 0 in c.TrackedPos() then StFalse()
          else
            var shiftByOne := Map(c.TrackedPos(), (pos: nat) =>  pos - 1);
            StCond(shiftByOne, c.TrackedVals())
        else if pushes == 1 && pops == 1 then
          if 0 in c.TrackedPos() then StFalse()
          else c
        else
          assert pushes == 0 && 3 <= pops <= 4;
          var shiftBy := Map(c.TrackedPos(), pos =>  pos + pops - pushes);
          StCond(shiftBy, c.TrackedVals())

      case MemOp(_, _, _, _, pushes, pops)      =>
        if pushes == 0 then
          assert pops == 2;
          var shiftByTwo := Map(c.TrackedPos(), pos =>  pos + 2);
          StCond(shiftByTwo, c.TrackedVals())
        else
          assert pushes == pops == 1;
          if 0 in c.TrackedPos() then StFalse()
          else c

      case StorageOp(_, _, _, _, pushes, pops)      =>
        if pushes == 0 then
          assert pops == 2;
          var shiftByTwo := Map(c.TrackedPos(), pos =>  pos + 2);
          StCond(shiftByTwo, c.TrackedVals())
        else
          assert pushes == pops == 1;
          if 0 in c.TrackedPos() then StFalse()
          else c

      case JumpOp(_, opcode, _, _, _, _)  =>
        if opcode == JUMPDEST then c
        else if JUMP <= opcode <= JUMPI then
          //    If JUMP +1, if JUMPI + 2
          var k := opcode - JUMP + 1;
          var shiftBy := Map(c.TrackedPos(), pos =>  pos + k as nat);
          StCond(shiftBy, c.TrackedVals())
        else  // RJUMPs not implemented
          StFalse()

      case RunOp(_, opcode, _, _, _, _)  =>
        if 0 in c.TrackedPos() then StFalse()
        else
          var shiftByOne := Map(c.TrackedPos(), (pos: nat) =>  pos - 1);
          StCond(shiftByOne, c.TrackedVals())

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
            if c.TrackedValAt(i) == argVal.Extract() then
              //  We can filter out position 0 as it is resolved
              var filtered := c.TrackedPos()[..i] + c.TrackedPos()[i + 1..];
              assert forall k:: 0 <= k < |c.TrackedPos()[..i]| ==> c.TrackedPos()[k] != c.TrackedPosAt(i);
              assert forall k {:triggers  filtered[k]}:: 0 <= k < |c.TrackedPos()[i + 1..]| ==> c.TrackedPos()[i + 1 + k] != c.TrackedPosAt(i);
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

      case LogOp(_, opcode, _, _, pushes, pops)  =>
        assert pushes == 0 && 2 <= pops <= 6;
        var shiftBy := Map(c.TrackedPos(), pos =>  pos + pops);
        StCond(shiftBy, c.TrackedVals())

      case SysOp(_, opcode, _, _, pushes, pops)  =>
        if pushes == 0 then
          var shiftBy := Map(c.TrackedPos(), pos =>  pos + pops);
          StCond(shiftBy, c.TrackedVals())
        else
          assert pushes == 1;
          if 0 in c.TrackedPos() then StFalse()
          else
            var shiftBy := Map(c.TrackedPos(), pos =>  pos + pops);
            StCond(shiftBy, c.TrackedVals())
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

  /** pencolour and background colour. */
  function Colours(i: ValidInstruction): (string, string)
  {
    match i.op
    case ArithOp(_, _, _, _, _, _) =>  ( "#316152", "#c6eb76")
    case CompOp(_, _, _, _, _, _) =>  ("darkgoldenrod", "bisque")
    case BitwiseOp(_, _, _, _, _, _) =>  ("orange", "#f3f383" )
    case KeccakOp(_, _, _, _, _, _) =>  ("grey", "linen")
    case EnvOp(_, _, _, _, _, _) =>  ("darkslategrey", "lightgrey")
    case MemOp(_, _, _, _, _, _) =>  ("sienna", "wheat")

    case StorageOp(_, _, _, _, _, _) =>  ("fuchsia", "mistyrose")
    case JumpOp(_, _, _, _, _, _) =>  ("purple", "thistle")
    case RunOp(_, _, _, _, _, _) =>  ("sienna", "tan")

    case StackOp(_, _, _, _, _, _) =>  ("royalblue", "powderblue")

    case LogOp(_, _, _, _, _, _) =>  ("cornflowerblue", "lavender")
    case SysOp(_, opcode, _, _, _, _) =>
      if opcode == STOP || opcode == REVERT then ("brown", "lightsalmon")
      else if opcode == RETURN then ("teal", "greenyellow")
      else if opcode == CALL || opcode == CALLCODE || opcode == DELEGATECALL || opcode == STATICCALL then
        ("sienna", "tan")
      else
        ("brown", "salmon")
  }
}
