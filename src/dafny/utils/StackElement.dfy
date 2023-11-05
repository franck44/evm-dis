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

/**
  *  Provides Abstract Stack e;ements.
  */
module StackElement {

  import opened Int

  /** The stack elements can be either concrete valies of unknown which is
    * captured by Random().
    */
  datatype StackElem = Value(v: u256) | Random(s: string := "") {

    function Extract(): u256 
        requires this.Value?
    {
        this.v
    }
  }

}
