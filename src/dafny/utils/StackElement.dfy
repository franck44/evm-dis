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

include "./int.dfy"
include "./Hex.dfy"

/**
  *  Provides Abstract Stack e;ements.
  */
module StackElement {

  import opened Int
  import opened Hex

  /** The stack elements can be either concrete valies of unknown which is
    * captured by Random().
    */
  datatype StackElem = Value(v: u256) | Random(s: string := "") {

    /**
      *  Pretty print a stack element.
      */
    function ToString(): string {
      match this
      case Value(v) => NatToString(v as nat) +
      "(0x" + NatToHex(v as nat) + ")"
      case Random(_) => "?"
    }

     function ToHTML(): string {
      match this
      case Value(v) => "(0x" + NatToHex(v as nat) + ")"
      case Random(_) => "?"
    }

    /**
      * Extract the value of a stack Value element.
      */
    function Extract(): u256
      requires this.Value?
    {
      this.v
    }
  }

  /**
    *  Pretty print a stack.
    */
  function StackToString(s: seq<StackElem>): string
  {
    if |s| == 0 then "Ø"
    else
      s[0].ToString() + "," + StackToString(s[1..])
  }


}
