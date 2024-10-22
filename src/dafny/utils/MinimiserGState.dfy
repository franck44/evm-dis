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


include "./Minimiser.dfy"
include "./CFGState.dfy"

/**  
  * Provides minimisation of finite deterministic automata
  * with states of type GState.
  */
module {:disableNonlinearArithmetic} GStateMinimiser refines Minimiser {

  import opened CFGState
  type T = CFGState.GState
  const DEFAULT_STATE := CFGState.DEFAULT_GSTATE

}