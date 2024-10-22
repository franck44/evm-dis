/*
 * Copyright 2024 Franck Cassez
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
include "../utils/LinSegments.dfy"
include "../utils/StackElement.dfy"

/**
  * Provides ability to generate Dafny code from segments.
  * 
  */
module SegBuilder {

  import opened EVMOpcodes
  import opened LinSegments
  import opened MiscTypes
  import opened Instructions
  import opened StackElement

  /**
    *   Try to resolve target address of a JUMP 
    */
  function JUMPResolver(s: ValidLinSeg): Either<StackElem, nat>
    requires s.JUMPSeg? || s.JUMPISeg?
  {
    // Track position of target address at Peek(0), and mark it as
    //  resolved if it is found constant in the segment.
    //  Start after the last non-jump instruction in the segment, use ins instead Ins().
    assert forall i:: 0 <= i < |s.ins| ==> s.ins[i].op.IsValid();
    StackPositionTracker(s.ins, 0)
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
  function StackPositionTracker(xs: seq<ValidInstruction>, pos: nat := 0): Either<StackElem, nat>
  {
    if |xs| == 0 then Right(pos)
    else
      //  Compute tracker on second last instruction
      var x := xs[|xs| - 1].StackPosBackWardTracker(pos);
      match x
      case Left(v) => Left(v)
      case Right(v) => StackPositionTracker(xs[..|xs| - 1], v)
  }

}

