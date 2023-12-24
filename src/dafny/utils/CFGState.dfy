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

include "../utils/StackElement.dfy"

/**
  *Provides control flow graph states.
  */
module CFGState {

  import opened StackElement

  const DEFAULT_GSTATE: GState := EGState(0, [])
  /**
    *   A CFG state.
    *   @param segNum   the segment number.
    *   @param st       the stack.
    */
  datatype GState = EGState(segNum: nat, st: seq<StackElem>) | ErrorGState(msg: string := "")
}


