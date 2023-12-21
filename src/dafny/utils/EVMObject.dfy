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
include "../utils/MiscTypes.dfy"
include "../utils/Instructions.dfy"
include "../utils/int.dfy"
include "../proofobjectbuilder/SegmentBuilder.dfy"
include "../utils/Hex.dfy"

/**
  *  Provides EVM Object.
  *  An EVM object is a list of segments together with some 
  *  additional information e.g. the jumpDests in the segments.
  */
module EVMObject {

  import opened LinSegments
  import opened State
  import opened MiscTypes
  import Instructions
  import Int
  import SegBuilder
  import Hex

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

    /**
      * Compute the next abstract states from a given abstract state.
      */
    function Next(s: AState): seq<AState>
    {
      if s.Error? then []
      else
        match PCToSeg(s.pc) {
          case Some(s0) =>
            var exit0 := if xs[s0].HasExit(false) then [xs[s0].Run(s, false, jumpDests)] else [];
            var exit1 := if xs[s0].HasExit(true) then [xs[s0].Run(s, true, jumpDests)] else [];
            exit0 + exit1
          case None => []
        }
    }

    /**
      * Generate the HTNL representation of a given abstract state.
      */
    function ToHTML(a: AState): string {
      if a.Error? then
        "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"
      else
        match PCToSeg(a.pc) {
          case Some(seg1) =>
            "<" + DOTSeg(xs[seg1], seg1).0 +">"
          case None =>  "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"
        }
    }

    /**
      *   Retrieve num of segment that correspond to a PC if any.
      */
    function PCToSeg(pc: nat, rank: nat := 0): (r: Option<nat>)
      requires rank <= |xs|
      ensures r.Some? ==> r.v < |xs|
      ensures r.Some?  ==> xs[r.v].StartAddress() == pc
      decreases |xs| - rank
    {
      if rank == |xs| then None
      else if xs[rank].StartAddress() == pc then Some(rank)
      else PCToSeg(pc, rank + 1)
    }

  }

  /**   Print the content of a segment. */
  function DOTSeg(s: ValidLinSeg, numSeg: nat): (string, string)
  {
    //  Jump target
    var jumpTip :=
      if s.JUMPSeg? || s.JUMPISeg? then
        var r := SegBuilder.JUMPResolver(s);
        match r {
          case Left(v) =>
            match v {
              case Value(address) => "&#10;Exit Jump target: Constant 0x" + Hex.NatToHex(address as nat)
              case Random(msg) => "&#10;Exit Jump target: Unknown"
            }
          case Right(stackPos) => "&#10;Exit Jump target: Stack on Entry.Peek(" + Int.NatToString(stackPos) +  ")"

        } else "";
    var stackSizeEffect := "Stack Size &#916;: " + Int.IntToString(s.StackEffect());
    var mninNumOpe := "&#10;Stack Size on Entry &#8805; " + Int.NatToString(s.WeakestPreOperands());
    var prefix := "<B>Segment "
                  + Int.NatToString(numSeg)
                  + " [0x"
                  + Hex.NatToHex(s.StartAddress())
                  + "]</B><BR ALIGN=\"CENTER\"/>\n";
    var body := Instructions.ToDot(s.Ins());
    (prefix + body, stackSizeEffect +  jumpTip + mninNumOpe)
  }

  /** Collect jumpdests in a list of segments.  */
  function CollectJumpDests(xs: seq<ValidLinSeg>): seq<nat> {
    if |xs| == 0 then []
    else
      xs[0].CollectJumpDest() + CollectJumpDests(xs[1..])
  }


}

