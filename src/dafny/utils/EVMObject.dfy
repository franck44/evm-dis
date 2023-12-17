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

include "../utils/LinSegments.dfy"
include "../utils/State.dfy"
include "../utils/CFGraph.dfy"

/**
  *  Provides EVM Object.
  *  An EVM object is a list of segments together with some 
  *  additional information e.g. the jumpDests in the segments.
  */
module EVMObject {

  import opened LinSegments
  import opened State
  import CFGraph

  /**   A valid EVMObj should have jumpdests consistent with the segments. */
  type ValidEVMObj = e: EVMObj | e.jumpDests == CollectJumpDests(e.xs)
    witness EVMObj([], [])

  /**   An EVMObj has segments and jumpDests. */
  datatype EVMObj = EVMObj(
    xs: seq<ValidLinSeg>,
    jumpDests: seq<nat> := CollectJumpDests(xs)) {

    /** A valid EVMObj has jumpDests consistent with xs. */
    predicate IsValid() {
      jumpDests == CollectJumpDests(xs)
    }

    /** The size of the program in bytes. */
    function Size(ls: seq<ValidLinSeg> := xs): nat {
      if |ls| == 0 then 0
      else ls[0].Size() + Size(ls[1..])
    }

    function Next(s: AState): seq<AState>
    {
      if s.Error? then []
      else
        match PCToSeg(xs, s.pc) {
          case Some(s0) =>
            var exit0 := if xs[s0].HasExit(false) then [xs[s0].Run(s, false, jumpDests)] else [];
            var exit1 := if xs[s0].HasExit(true) then [xs[s0].Run(s, true, jumpDests)] else [];
            exit0 + exit1
          case None => []
        }
    }

    function ToHTML(a: AState): string {
      if a.Error? then
        "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"
      else
        match PCToSeg(xs, a.pc) {
          case Some(seg1) =>
            "<" + CFGraph.DOTSeg(xs[seg1], seg1).0 +">"
          case None =>  "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"
        }
    }
  }



  /** Collect jumpdests in a list of segments.  */
  function CollectJumpDests(xs: seq<ValidLinSeg>): seq<nat> {
    if |xs| == 0 then []
    else
      xs[0].CollectJumpDest() + CollectJumpDests(xs[1..])
  }


}

