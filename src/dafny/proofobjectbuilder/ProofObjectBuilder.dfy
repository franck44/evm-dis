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
include "../utils/ProofObject.dfy"
include "./SegmentBuilder.dfy"

/**
  *  Provides proof objects.
  */
module ProofObjectBuilder {

  import opened MiscTypes
  import opened LinSegments
  import opened ProofObject
  import SegBuilder

  /**
    *    Given a linear segment, build a proof object.
    */
  function BuildProofObject(x: LinSeg): ProofObject
  {
    var wpOp := x.WeakestPreOperands(0);
    var wpCap := x.WeakestPreCapacity(0);
    if x.JUMPSeg? || x.JUMPISeg? then
      var tgt :=  SegBuilder.JUMPResolver(x);
      JUMP(x, wpOp, wpCap, tgt)
    else
      TERMINAL(x, wpOp, wpCap)
  }
}

