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

include "../utils/MiscTypes.dfy"
include "../utils/LinSegments.dfy"

/**
  *  Provides proof objects types.
  */
module ProofObject {

  import opened MiscTypes
  import opened LinSegments

  /**
    *   Either a segment terninating with a JUMP or a segment terminating with a STOP/RETURN/REVERT
    */
  datatype ProofObject =
    |  JUMP(s: LinSeg, wpOp: Option<nat>, wpCap: Option<nat>, tgt: Either<seq<char>, nat>)
    |  TERMINAL(s: LinSeg, wpOp: Option<nat>, wpCap: Option<nat>)

}

