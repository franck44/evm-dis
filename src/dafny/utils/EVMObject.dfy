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
include "../utils/Automata.dfy"
include "../utils/Partition.dfy"
include "../utils/MinimiserAState.dfy"
include "../CFGBuilder/BuildCFGSimplified.dfy"

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
  import Automata
  import opened DFSSimple
  import opened PartitionMod
  import opened AStateMinimiser


  /**   A valid EVMObj should have jumpdests consistent with the segments. */
  type ValidEVMObj = e: EVMObj | e.jumpDests == CollectJumpDests(e.xs)
    witness EVMObj([], [])

  /**   An EVMObj has segments and jumpDests. */
  datatype EVMObj = EVMObj(
    xs: seq<ValidLinSeg>,
    jumpDests: seq<nat> := CollectJumpDests(xs)) {

    /** A valid EVMObj has jumpDests consistent with xs. */
    predicate IsValid() {
      && (forall i, i':: 0 <= i < i' < |xs| ==> xs[i].StartAddress() < xs[i'].StartAddress())
    //   && jumpDests == CollectJumpDests(xs)
    //   && startAddresses == CollectStartAddresses(xs)
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
            seq(xs[s0].NumberOfExits(), i requires 0 <= i < xs[s0].NumberOfExits() => xs[s0].Run(s, i, jumpDests))
          case None => []
        }
    }

    /**
      * Build the CFG of the EVMObj.
      * The CFG is built by running a DFS from the initial state.
      * @param maxDepth The maximum depth of the DFS.
      * @param minimise If true, the CFG is minimised.   
      */
    method BuildCFG(maxDepth: nat := 100, minimise: bool := true) returns (a: Automata.ValidAuto<AState>)
    {
      //  For now we ignore the history
      var a1, _ := DFS(
        Next,
        DEFAULT_VALIDSTATE,
        History(DEFAULT_VALIDSTATE, [DEFAULT_VALIDSTATE]),
        Automata.Auto(),
        maxDepth);
      if !minimise || a1.SSize() == 0 {
        return a1;
      } else {
        var p1: ValidPartition := PartitionMod.MakeInit(a1.SSize());
        //  create an equivalence relation on nodes
        var e :=
          (x:nat, y:nat) requires 0 <= x < a1.SSize() && 0 <= y < a1.SSize()
          => if x == y then
              true
            else
              match (a1.states[x], a1.states[y])
              case (EState(pc1,_), EState(pc2, _)) => PCToSeg(pc1).Some? && PCToSeg(pc2).Some? && pc1 == pc2
              case (_, _) => false
          ;
        assert IsEquivRel(e, a1.SSize());
        var p2 := p1.ComputeFinest(e);

        var vp: AStateMinimiser.Pair := Pair(a1, p2);
        var a2 := vp.Minimise();
        return a2;
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

