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

include "../../../src/dafny/utils/State.dfy"
include "../../../src/dafny/utils/LinSegments.dfy"
include "../../../src/dafny/utils/CFGraph.dfy"

/**
  * Computation of the CFG via some DFS.
  */
module BuildCFGraph {

  import opened MiscTypes
  import opened LinSegments
  import opened State
  import opened CFGraph

  /**
    *   1. First add path to state 
    *   2. if similar state already encountered check 
    *       whether it covers the new one. Use the most ancient
    *       one.
    *   3. add tests for all states that are similar not only most
    *       ancient one.
    */
  function BuildCFGV4(xs: seq<ValidLinSeg>, maxDepth: nat, numSeg: nat := 0, s: ValidState := DEFAULT_VALIDSTATE, seen: seq<CFGNode> := [CFGNode([], Some(0))], seenPCs: seq<nat> := [0], path: seq<bool> := []): (g: BoolCFGraph)
    requires numSeg < |xs|
    requires forall k:: k in seen && k.seg.Some? ==> k.seg.v < |xs|
    requires |seen| == |seenPCs| == |path| + 1
    requires forall k:: 0 <= k < |seen| ==> seen[k].id == path[..k]
    requires forall k:: 0 <= k < |seen| ==> seen[k].seg.Some?
    requires s.PC() == seenPCs[|seenPCs| - 1]
    requires forall k:: 0 <= k < |seen| ==> seenPCs[k] == xs[seen[k].seg.v].StartAddress()

    ensures forall k:: k in seen && k.seg.Some? ==> k.seg.v < |xs|
    ensures forall k:: k in g.edges ==> k.src.seg.Some? ==> 0 <= k.src.seg.v < |xs|
    ensures forall k:: k in g.edges ==> k.tgt.seg.Some? ==> 0 <= k.tgt.seg.v < |xs|

    ensures |seen| == |seenPCs| == |path| + 1
    ensures forall k:: 0 <= k < |seen| ==> seen[k].id == path[..k]
    ensures forall k:: 0 <= k < |seen| ==> seen[k].seg.Some?
    ensures s.PC() == seenPCs[|seenPCs| - 1]
    ensures forall k:: 0 <= k < |seen| ==> seenPCs[k] == xs[seen[k].seg.v].StartAddress()

    decreases maxDepth
  {
    if maxDepth == 0 then
      //  Indicate maxdepth reached by a loop
      BoolCFGraph([BoolEdge(CFGNode(path, Some(numSeg)), true, CFGNode(path, Some(numSeg)))])
    else if !xs[numSeg].HasExit(false) && !xs[numSeg].HasExit(true) then
      //  no successors
      BoolCFGraph([])
    else
      //  DFS false
      var leftBranch :=
        if xs[numSeg].HasExit(false) then
          var leftSucc := xs[numSeg].Run(s, false);
          if leftSucc.EState? then
            var nextSeg := PCToSeg(xs, leftSucc.PC());
            if nextSeg.Some? then
              var src := CFGNode(path, Some(numSeg));
              var tgt := CFGNode(path + [false], nextSeg);
              var gleft := BuildCFGV4(xs, maxDepth - 1, nextSeg.v, leftSucc, seen + [tgt], seenPCs + [leftSucc.PC()], path + [false]);
              gleft.AddEdge(BoolEdge(src, false, tgt))
            else  //  Next segment could not be found
              BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), false, CFGNode(path + [false])) ])
          else // left successor of segment resulted in Error state
            BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), false, CFGNode(path + [false])) ])
        else // no false exit branch expected for this segment
          BoolCFGraph([ ]) ;

      //  DFS true
      var rightBranch :=
        if xs[numSeg].HasExit(true) then
          var rightSucc := xs[numSeg].Run(s, true);
          if rightSucc.EState?  then
            var nextSeg := PCToSeg(xs, rightSucc.PC());
            //  Check if this pc has been seen before
            if nextSeg.Some? then
              //  Check if a previous CFGNode covers this node
              if rightSucc.PC() !in seenPCs then
                var src := CFGNode(path, Some(numSeg));
                var tgt := CFGNode(path + [true], nextSeg);
                var gright := BuildCFGV4(xs, maxDepth - 1, nextSeg.v, rightSucc, seen + [tgt], seenPCs + [rightSucc.PC()],path + [true]);
                gright.AddEdge(BoolEdge(src, true, tgt))
              else
                //  We have seen this PC before. Link to the first CFGNode in the list
                //  with this PC
                match SafeLoopFound(xs, rightSucc.PC(), seen)
                case Some(prev) =>
                  assert prev.seg.v < |xs|;
                  BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), true, prev)])
                case None =>
                  BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), true,  CFGNode(path + [true]))])
            else // Next segment could not be found
              BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), true, CFGNode(path + [true])) ])
          else // right successor of segment resulted in Error state
            BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), true, CFGNode(path + [true])) ])
        else //
          BoolCFGraph([ ]) ;

      BoolCFGraph(leftBranch.edges + rightBranch.edges)

  }

  //  Helpers

  /**
    *   Retrieve num of segments that correspond to a PC if any.
    */
  function PCToSeg(xs: seq<ValidLinSeg>, pc: nat, rank: nat := 0): (r: Option<nat>)
    requires rank <= |xs|
    ensures r.Some? ==> r.v < |xs|
    ensures r.Some?  ==> xs[r.v].StartAddress() == pc 
    decreases |xs| - rank
  {
    if rank == |xs| then None
    else if xs[rank].StartAddress() == pc then Some(rank)
    else PCToSeg(xs, pc, rank + 1)
  }

  function FindFirstNodeWithPC(xs: seq<ValidLinSeg>, pc: nat, s: seq<CFGNode>, index: nat := 0): (r: Option<(CFGNode, nat)>)
    requires |xs| >= 1
    requires index <= |s|
    requires forall k:: k in s && k.seg.Some? ==> k.seg.v < |xs|

    ensures r.Some? ==> index < |s|
    ensures r.Some? ==> r.v.0.seg.Some? && r.v.0.seg.v < |xs| 
    ensures r.Some? ==> r.v.0.seg.Some? &&  r.v.1 < |s|
    ensures r.Some? ==> xs[r.v.0.seg.v].StartAddress() == pc

    decreases |s| - index
  {
    if |s| == index then None
    else if s[index].seg.Some? && xs[s[index].seg.v].StartAddress() == pc then Some((s[index], index))
    else FindFirstNodeWithPC(xs, pc, s, index + 1)
  }

  /**
    *   Check if pc has been seen before, and whether we can loop back to an already seen
    *   CFGNode on this path.
    */
  function SafeLoopFound(xs: seq<ValidLinSeg>, pc: nat, seenOnPath: seq<CFGNode>): Option<CFGNode>
    requires |xs| >= 1
    requires forall k:: k in seenOnPath && k.seg.Some? ==> k.seg.v < |xs|
  {
    match FindFirstNodeWithPC(xs, pc, seenOnPath)
    case Some(v) => 
        //  some properties must hold on the path defined by the index v.1
        // var init := seenOnPath[];
        Some(v.0)
    case None => None
    //  collect index of the node in the sequence
    // Compute WPre to
  }

}

