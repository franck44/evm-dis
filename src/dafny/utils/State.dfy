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
include "./StackElement.dfy"

/**
  *  Provides Abstract States.
  */
module State {

  import opened Int
  import opened Hex
  import opened StackElement

  /** The stack elements can be either concrete valies of unknown which is
    * captured by Random().
    */
  //   datatype StackElem = Value(v: u256) | Random(s: string := "")

  /**
    *   A ValidState is a state from whihc we can execute an instruction.
    */
  type ValidState = s: AState | s.EState? witness DEFAULT_VALIDSTATE


  const DEFAULT_VALIDSTATE := EState(0, [])
  /**
    *   There are two types of abstract types: an 'executing' state from
    *   from which can execute the code and Error states from which we cannot.
    *   
    *   @param  pc      For an executing state it is the current value of pc.
    *   @param  stack   For an executing state, the current value of the stack.
    */
  datatype AState = EState(pc: nat, stack: seq<StackElem>)
                  | Error(msg: string := "Error")
  {

    function ToString(): string
    {
      match this
      case EState(pc, stack) =>
        "(pc=0x" + NatToHex(pc) + " stack:[" + StackToString(stack) + "])"
      case Error(m) => "ErrorState " + m
    }

    /** Size of the stack. */
    function Size(): nat
      requires this.EState?
    {
      |this.stack|
    }

    /** Current PC. */
    function PC(): nat
      requires this.EState?
    {
      pc
    }

    /** Advance pc by n. */
    function Skip(n: nat): AState
      requires this.EState?
    {
      this.(pc := this.pc + n)
    }

    /** Advance pc to tgt. */
    function Goto(tgt: nat): AState
      requires this.EState?
    {
      this.(pc := tgt)
    }

    /** Get the k-th element on the stack. */
    function Peek(k: nat): StackElem
      requires this.EState?
      requires this.Size() > k

    {
      this.stack[k]
    }

    /** Pop one element. */
    function Pop(): AState
      requires this.EState?
      requires this.Size() >= 1
    {
      this.PopN(1)
    }

    /** Pop n elements. */
    function PopN(n: nat): AState
      requires this.EState?
      requires this.Size() >= n
    {
      this.(stack := this.stack[n..])
    }

    /** Push to the top of the stack. */
    function Push(v: StackElem): AState
      requires this.EState?
    {
      this.(stack := [v] + this.stack)
    }

    /** Push n random values. */
    function PushNRandom(n: nat): AState
      requires this.EState?
    {
      var xr := seq(n, _ => Random());
      this.(stack := xr + this.stack)
    }

    /** Duplicate element n. Push a copy of Peek(n). */
    function Dup(n: nat): AState
      requires this.EState?
      requires 1 <= n <= 16
      requires this.Size() >= n > 0
    {
      var nth := this.stack[n - 1];
      this.(stack := [nth] + this.stack)
    }

    /** Swap Peek(n) and Peek(0). */
    function Swap(n: nat): AState
      requires this.EState?
      requires 1 <= n <= 16
      requires this.Size() > n > 0
    {
      var nth := this.stack[n];
      var top := this.stack[0];
      this.(stack := this.stack[0 := nth][n := top])
    }

  }

  //    Helpers
  function StackToString(s: seq<StackElem>): string
  {
    if |s| == 0 then ""
    else
      s[0].ToString() + "," + StackToString(s[1..])
  }

   /**
      * Build an initial state that satisfies a given condition.
      * @param  c       A valid condition.
      * @param  initpc  An optional initial value for the pc.
      * @returns        A valid  state with a (minimal) stack that satisfies c and
      *                 init value for pc.
      */
    function BuildInitState(c: ValidCond, initpc: nat := 0): (s: ValidState)
      requires !c.StFalse?
    {
      var s0 := DEFAULT_VALIDSTATE;
      if c.StCond? then
        s0.(stack := c.BuildStack(), pc := initpc)
      else
        s0.(pc := initpc)
    }



}
