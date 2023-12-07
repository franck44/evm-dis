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
include "./LoopResolver.dfy"
  /**
    * Computation of the CFG via some DFS.  
    */
module BuildCFGraph {

  import opened MiscTypes
  import opened LinSegments
  import opened State
  import opened CFGraph
  import opened WeakPre
  import opened LoopResolver

  /**
    *   1. First add path to state 
    *   2. if similar state already encountered check 
    *       whether it covers the new one. Use the most ancient
    *       one.
    *   3. add tests for all states that are similar not only most
    *       ancient one.
    */
  function BuildCFGV5(xs: seq<ValidLinSeg>, maxDepth: nat, jumpDests: seq<nat>, numSeg: nat := 0, s: ValidState := DEFAULT_VALIDSTATE, seen: seq<CFGNode> := [CFGNode([], Some(0))], seenPCs: seq<nat> := [0], path: seq<bool> := [], seenStates: map<AState, CFGNode> := map[DEFAULT_VALIDSTATE := CFGNode([], Some(0))]): (r :(BoolCFGraph,  map<AState, CFGNode>))
    requires numSeg < |xs|
    requires forall k:: k in seen && k.seg.Some? ==> k.seg.v < |xs|
    requires |seen| == |seenPCs| == |path| + 1
    requires forall k:: 0 <= k < |seen| ==> seen[k].id == path[..k]
    requires forall k:: 0 <= k < |seen| ==> seen[k].seg.Some?
    requires s.PC() == seenPCs[|seenPCs| - 1]
    requires forall k:: 0 <= k < |seen| ==> seenPCs[k] == xs[seen[k].seg.v].StartAddress()
    requires seen[|seen| - 1].seg.v == numSeg
    requires forall s:: s in seenStates && seenStates[s].seg.Some? ==> seenStates[s].seg.v < |xs|
    requires s in seenStates

    ensures forall k:: k in seen && k.seg.Some? ==> k.seg.v < |xs|
    ensures forall k:: k in r.0.edges ==> k.src.seg.Some? ==> 0 <= k.src.seg.v < |xs|
    ensures forall k:: k in r.0.edges ==> k.tgt.seg.Some? ==> 0 <= k.tgt.seg.v < |xs|
    ensures r.0.IsValid()

    ensures |seen| == |seenPCs| == |path| + 1
    ensures forall k:: 0 <= k < |seen| ==> seen[k].id == path[..k]
    ensures forall k:: 0 <= k < |seen| ==> seen[k].seg.Some?
    ensures s.PC() == seenPCs[|seenPCs| - 1]
    ensures forall k:: 0 <= k < |seen| ==> seenPCs[k] == xs[seen[k].seg.v].StartAddress()
    ensures forall s:: s in r.1 && r.1[s].seg.Some? ==> r.1[s].seg.v < |xs|

    decreases maxDepth
  {

    if !xs[numSeg].HasExit(false) && !xs[numSeg].HasExit(true) then
      //  no successors
      (BoolCFGraph([], 0), seenStates)
    else if maxDepth == 0 then
      //  Indicate maxdepth reached by a loop
      (BoolCFGraph([BoolEdge(CFGNode(path, Some(numSeg)), true, CFGNode(path, Some(numSeg)))], |xs| - 1), seenStates)
    else
      //  DFS false
      var leftBranch :=
        if xs[numSeg].HasExit(false) then
          var leftSucc := xs[numSeg].Run(s, false, jumpDests);
          //    leftSucc is the successor state of s via false
          if leftSucc in seenStates then
            //  We have already seen this state, retrieve node that corresponds to this state and
            //  create an edge to it
            assert seenStates[leftSucc].seg.Some? ==> seenStates[leftSucc].seg.v < |xs|;
            (BoolCFGraph( [BoolEdge(CFGNode(path, Some(numSeg)), false, seenStates[leftSucc])]), seenStates)
          else if leftSucc.EState? && leftSucc.PC() < Int.TWO_256 then
            var nextSeg := PCToSeg(xs, leftSucc.PC());
            if nextSeg.Some? then
              var src := CFGNode(path, Some(numSeg));
              var tgt := CFGNode(path + [false], nextSeg);
              var newSeenSegs := seenStates[leftSucc := tgt];
              var gleft := BuildCFGV5(xs, maxDepth - 1, jumpDests, nextSeg.v, leftSucc, seen + [tgt], seenPCs + [leftSucc.PC()], path + [false], newSeenSegs);
              (gleft.0.AddEdge(BoolEdge(src, false, tgt)), gleft.1)
            else  //  Next segment could not be found
              (BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), false, CFGNode(path + [false])) ]), seenStates)
          else // left successor of segment resulted in Error state
            (BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), false, CFGNode(path + [false])) ]), seenStates)
        else // no false exit branch expected for this segment
          (BoolCFGraph([ ]), seenStates) ;

      //  The right branch takes into account the states seen in the left branch
      var newSeenStates := leftBranch.1;

      //  DFS true
      var rightBranch :=
        if xs[numSeg].HasExit(true) then
          //  We must be in a JUMP or JUMPI segment
          assert xs[numSeg].JUMPSeg? || xs[numSeg].JUMPISeg?;
          var rightSucc := xs[numSeg].Run(s, true, jumpDests);
          if rightSucc.EState?  && rightSucc.PC() < Int.TWO_256 then
            var nextSeg := PCToSeg(xs, rightSucc.PC());
            //  Check if this pc has been seen before
            if nextSeg.Some? then
              //  Check if a previous CFGNode potentially covers this node
              if rightSucc in newSeenStates then
                //  We have already seen this state
                assert newSeenStates[rightSucc].seg.Some? ==> newSeenStates[rightSucc].seg.v < |xs|;
                (BoolCFGraph( [BoolEdge(CFGNode(path, Some(numSeg)), true, newSeenStates[rightSucc])]), newSeenStates)
              else if rightSucc.PC() !in seenPCs then
                //  We have not seen this segment.pc before, continue to unfold
                var src := CFGNode(path, Some(numSeg));
                var tgt := CFGNode(path + [true], nextSeg);
                var newSeenSegs := newSeenStates[rightSucc := tgt];
                var gright := BuildCFGV5(xs, maxDepth - 1, jumpDests, nextSeg.v, rightSucc, seen + [tgt], seenPCs + [rightSucc.PC()],path + [true], newSeenSegs);
                (gright.0.AddEdge(BoolEdge(src, true, tgt)), gright.1)
              else
                //  We have seen this PC before. Link to the first CFGNode in the list
                //  with this PC if there is one.
                match SafeLoopFound(xs, rightSucc.PC(), seen, path + [true], jumpDests) // , path + [true])
                case Some(prev) =>
                  // the computation for this path sopts. We have discovered a
                  //    lasso with the loop part being invariant under
                  //    reachable PCs.
                  assert prev.seg.Some?;
                  assert prev.seg.v < |xs|;
                  (BoolCFGraph([BoolEdge(CFGNode(path, Some(numSeg)), true, prev)], |xs|), newSeenStates)
                case None =>
                  //  Progress the DFS with a new node
                  var src := CFGNode(path, Some(numSeg));
                  var tgt := CFGNode(path + [true], nextSeg);
                  var newSeenSegs := newSeenStates[rightSucc := tgt];
                  var gright := BuildCFGV5(xs, maxDepth - 1, jumpDests, nextSeg.v, rightSucc, seen + [tgt], seenPCs + [rightSucc.PC()], path + [true], newSeenSegs);
                  (gright.0.AddEdge(BoolEdge(src, true, tgt)), gright.1)
            else // Next segment could not be found
              (BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), true, CFGNode(path + [true])) ]), newSeenStates)
          else // right successor of segment resulted in Error state
            (BoolCFGraph([ BoolEdge(CFGNode(path, Some(numSeg)), true, CFGNode(path + [true])) ]), newSeenStates)
        else //
          (BoolCFGraph([ ], 0), newSeenStates) ;
      (BoolCFGraph(leftBranch.0.edges + rightBranch.0.edges, |xs| - 1), rightBranch.1)
  }

}

