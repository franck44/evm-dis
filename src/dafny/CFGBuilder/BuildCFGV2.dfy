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

    datatype History = 
        History(seen: seq<CFGNode>,  seenPCs: seq<nat>, path: seq<bool>, seenStates: map<AState, CFGNode>)

    datatype Context = Context(xs: seq<ValidLinSeg>, jumpDests: seq<nat>) 
    

  /**
    *   1. First add path to state 
    *   2. if similar state already encountered check 
    *       whether it covers the new one. Use the most ancient
    *       one.
    *   3. add tests for all states that are similar not only most
    *       ancient one.
    */
  function BuildCFGV5(c: Context, maxDepth: nat,  numSeg: nat := 0, s: ValidState := DEFAULT_VALIDSTATE, 
    h: History)

    // xs: seq<ValidLinSeg>, maxDepth: nat, jumpDests: seq<nat>, numSeg: nat := 0, s: ValidState := DEFAULT_VALIDSTATE, seen: seq<CFGNode> := [CFGNode([], Some(0))], seenPCs: seq<nat> := [0], path: seq<bool> := [], seenStates: map<AState, CFGNode> := map[DEFAULT_VALIDSTATE := CFGNode([], Some(0))])
    : (r :(BoolCFGraph,  map<AState, CFGNode>))
    requires numSeg < |c.xs|
    requires forall k:: k in h.seen && k.seg.Some? ==> k.seg.v < |c.xs|
    requires |h.seen| == |h.seenPCs| == |h.path| + 1
    requires forall k:: 0 <= k < |h.seen| ==> h.seen[k].id == h.path[..k]
    requires forall k:: 0 <= k < |h.seen| ==> h.seen[k].seg.Some?
    requires s.PC() == h.seenPCs[|h.seenPCs| - 1]
    requires forall k:: 0 <= k < |h.seen| ==> h.seenPCs[k] == c.xs[h.seen[k].seg.v].StartAddress()
    requires h.seen[|h.seen| - 1].seg.v == numSeg
    requires forall s:: s in h.seenStates && h.seenStates[s].seg.Some? ==> h.seenStates[s].seg.v < |c.xs|
    requires s in h.seenStates

    ensures forall k:: k in h.seen && k.seg.Some? ==> k.seg.v < |c.xs|
    ensures forall k:: k in r.0.edges ==> k.src.seg.Some? ==> 0 <= k.src.seg.v < |c.xs|
    ensures forall k:: k in r.0.edges ==> k.tgt.seg.Some? ==> 0 <= k.tgt.seg.v < |c.xs|
    ensures r.0.IsValid()

    ensures |h.seen| == |h.seenPCs| == |h.path| + 1
    ensures forall k:: 0 <= k < |h.seen| ==> h.seen[k].id == h.path[..k]
    ensures forall k:: 0 <= k < |h.seen| ==> h.seen[k].seg.Some?
    ensures s.PC() == h.seenPCs[|h.seenPCs| - 1]
    ensures forall k:: 0 <= k < |h.seen| ==> h.seenPCs[k] == c.xs[h.seen[k].seg.v].StartAddress()
    ensures forall s:: s in r.1 && r.1[s].seg.Some? ==> r.1[s].seg.v < |c.xs|

    decreases maxDepth
  {

    if !c.xs[numSeg].HasExit(false) && !c.xs[numSeg].HasExit(true) then
      //  no successors
      (BoolCFGraph([], 0), h.seenStates)
    else if maxDepth == 0 then
      //  Indicate maxdepth reached by a loop
      (BoolCFGraph([BoolEdge(CFGNode(h.path, Some(numSeg)), true, CFGNode(h.path, Some(numSeg)))], |c.xs| - 1), h.seenStates)
    else
      //  DFS false
      var leftBranch :=
        if c.xs[numSeg].HasExit(false) then
          var leftSucc := c.xs[numSeg].Run(s, false, c.jumpDests);
          //    leftSucc is the successor state of s via false
          if leftSucc in h.seenStates then
            //  We have already seen this state, retrieve node that corresponds to this state and
            //  create an edge to it
            assert h.seenStates[leftSucc].seg.Some? ==> h.seenStates[leftSucc].seg.v < |c.xs|;
            (BoolCFGraph( [BoolEdge(CFGNode(h.path, Some(numSeg)), false, h.seenStates[leftSucc])]), h.seenStates)
          else if leftSucc.EState? && leftSucc.PC() < Int.TWO_256 then
            var nextSeg := PCToSeg(c.xs, leftSucc.PC());
            if nextSeg.Some? then
              var src := CFGNode(h.path, Some(numSeg));
              var tgt := CFGNode(h.path + [false], nextSeg);
              var newSeenSegs := h.seenStates[leftSucc := tgt];
              var gleft := BuildCFGV5(c.xs, maxDepth - 1, c.jumpDests, nextSeg.v, leftSucc, h.seen + [tgt], h.seenPCs + [leftSucc.PC()], h.path + [false], newSeenSegs);
              (gleft.0.AddEdge(BoolEdge(src, false, tgt)), gleft.1)
            else  //  Next segment could not be found
              (BoolCFGraph([ BoolEdge(CFGNode(h.path, Some(numSeg)), false, CFGNode(h.path + [false])) ]), h.seenStates)
          else // left successor of segment resulted in Error state
            (BoolCFGraph([ BoolEdge(CFGNode(h.path, Some(numSeg)), false, CFGNode(h.path + [false])) ]), h.seenStates)
        else // no false exit branch expected for this segment
          (BoolCFGraph([ ]), h.seenStates) ;

      //  The right branch takes into account the states seen in the left branch
      var newSeenStates := leftBranch.1;

      //  DFS true
      var rightBranch :=
        if c.xs[numSeg].HasExit(true) then
          //  We must be in a JUMP or JUMPI segment
          assert c.xs[numSeg].JUMPSeg? || c.xs[numSeg].JUMPISeg?;
          var rightSucc := c.xs[numSeg].Run(s, true, c.jumpDests);
          if rightSucc.EState?  && rightSucc.PC() < Int.TWO_256 then
            var nextSeg := PCToSeg(c.xs, rightSucc.PC());
            //  Check if this pc has been seen before
            if nextSeg.Some? then
              //  Check if a previous CFGNode potentially covers this node
              if rightSucc in newSeenStates then
                //  We have already seen this state
                assert newSeenStates[rightSucc].seg.Some? ==> newSeenStates[rightSucc].seg.v < |c.xs|;
                (BoolCFGraph( [BoolEdge(CFGNode(h.path, Some(numSeg)), true, newSeenStates[rightSucc])]), newSeenStates)
              else if rightSucc.PC() !in h.seenPCs then
                //  We have not seen this segment.pc before, continue to unfold
                var src := CFGNode(h.path, Some(numSeg));
                var tgt := CFGNode(h.path + [true], nextSeg);
                var newSeenSegs := newSeenStates[rightSucc := tgt];
                var gright := BuildCFGV5(c.xs, maxDepth - 1, c.jumpDests, nextSeg.v, rightSucc, h.seen + [tgt], h.seenPCs + [rightSucc.PC()],h.path + [true], newSeenSegs);
                (gright.0.AddEdge(BoolEdge(src, true, tgt)), gright.1)
              else
                //  We have seen this PC before. Link to the first CFGNode in the list
                //  with this PC if there is one.
                match SafeLoopFound(c.xs, rightSucc.PC(), h.seen, h.path + [true], c.jumpDests) // , h.path + [true])
                case Some(prev) =>
                  // the computation for this h.path sopts. We have discovered a
                  //    lasso with the loop part being invariant under
                  //    reachable PCs.
                  assert prev.seg.Some?;
                  assert prev.seg.v < |c.xs|;
                  (BoolCFGraph([BoolEdge(CFGNode(h.path, Some(numSeg)), true, prev)], |c.xs|), newSeenStates)
                case None =>
                  //  Progress the DFS with a new node
                  var src := CFGNode(h.path, Some(numSeg));
                  var tgt := CFGNode(h.path + [true], nextSeg);
                  var newSeenSegs := newSeenStates[rightSucc := tgt];
                  var gright := BuildCFGV5(c.xs, maxDepth - 1, c.jumpDests, nextSeg.v, rightSucc, h.seen + [tgt], h.seenPCs + [rightSucc.PC()], h.path + [true], newSeenSegs);
                  (gright.0.AddEdge(BoolEdge(src, true, tgt)), gright.1)
            else // Next segment could not be found
              (BoolCFGraph([ BoolEdge(CFGNode(h.path, Some(numSeg)), true, CFGNode(h.path + [true])) ]), newSeenStates)
          else // right successor of segment resulted in Error state
            (BoolCFGraph([ BoolEdge(CFGNode(h.path, Some(numSeg)), true, CFGNode(h.path + [true])) ]), newSeenStates)
        else //
          (BoolCFGraph([ ], 0), newSeenStates) ;
      (BoolCFGraph(leftBranch.0.edges + rightBranch.0.edges, |c.xs| - 1), rightBranch.1)
  }

}

