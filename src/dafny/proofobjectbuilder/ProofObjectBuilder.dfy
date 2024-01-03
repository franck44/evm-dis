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
  function BuildProofObject(xs: seq<LinSeg>): (r: seq<ProofObj>)
    requires forall i:: 0 <= i < |xs| ==> xs[i].IsValid()
    ensures |xs| == |r|
    ensures forall i:: 0 <= i < |r| ==> r[i].IsValid()
  {
    if |xs| == 0 then []
    else
      var wpOp := xs[0].WeakestPreOperands();
      var wpCap := xs[0].WeakestPreCapacity(0);
      var obj :=
        (if xs[0].JUMPSeg? || xs[0].JUMPISeg? then
           var tgt :=  SegBuilder.JUMPResolver(xs[0]);
           JUMP(xs[0], wpOp, wpCap, tgt)
         else if xs[0].CONTSeg? then
           CONT(xs[0], wpOp, wpCap)
         else
           TERMINAL(xs[0], wpOp, wpCap)
        );
      [obj] + BuildProofObject(xs[1..])
  }
}

