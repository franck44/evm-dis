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
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/LinSegments.dfy"
include "../../../src/dafny/utils/CFGraph.dfy"
include "../../../src/dafny/utils/EVMObject.dfy"
include "./LoopResolver.dfy"
include "../../../src/dafny/utils/Statistics.dfy"
include "../../../src/dafny/utils/DFS.dfy"

/**
  * Computation of the CFG via some DFS.  
  */
module BuildCFGraph {

  import opened MiscTypes
  import Int
  import opened LinSegments
  import opened State
  import opened CFGraph
  import opened WeakPre
  import opened LoopResolver
  import opened EVMObject
  import opened Statistics
  import opened DFS

  /**  CFG computation  */
  datatype CFGComputation = CFGComputation(
    grph: BoolCFGraph,
    states:  map<AState, CFGNode>) {

    function Graph(): BoolCFGraph {
      grph
    }

    function VisitedStates(): map<AState, CFGNode> {
      states
    }
  }

  /**
    *   1. First add path to state 
    *   2. if similar state already encountered check 
    *       whether it covers the new one. Use the most ancient
    *       one.
    *   3. add tests for all states that are similar not only most
    *       ancient one.
    */
  function BuildCFGV6(
    c: EVMObj,
    maxDepth: nat,
    numSeg: nat := 0,
    s: ValidState := DEFAULT_VALIDSTATE,
    pathHistory: PathHistory := DEFAULT_PATH_HISTORY,
    searchHistory: DFSHistory := DEFAULT_DFS_HISTORY,
    stat: Stats := DEFAULT_STATS): (r:(CFGComputation, Stats))
    requires numSeg < |c.xs|
    requires pathHistory.IsConsistent(c, s)
    requires pathHistory.seen[|pathHistory.seen| - 1].seg.v == numSeg
    requires searchHistory.IsConsistent(c, s)
    requires pathHistory.seenStates == searchHistory.visitedStates

    ensures forall k:: k in r.0.grph.edges ==> k.src.seg.Some? ==> 0 <= k.src.seg.v < |c.xs|
    ensures forall k:: k in r.0.grph.edges ==> k.tgt.seg.Some? ==> 0 <= k.tgt.seg.v < |c.xs|
    ensures r.0.grph.IsValid()
    ensures forall s:: s in r.0.states && r.0.states[s].seg.Some? ==> r.0.states[s].seg.v < |c.xs|

    decreases maxDepth
  {

    if !c.xs[numSeg].HasExit(false) && !c.xs[numSeg].HasExit(true) then
      //  no successors
      assert pathHistory.seenStates == searchHistory.visitedStates;
      (CFGComputation(BoolCFGraph([], 0), searchHistory.visitedStates), stat)
    else if maxDepth == 0 then
      assert pathHistory.seenStates == searchHistory.visitedStates;
      //  Indicate maxdepth reached by a loop
      (CFGComputation(BoolCFGraph([BoolEdge(CFGNode(pathHistory.path, Some(numSeg)), true, CFGNode(pathHistory.path, Some(numSeg)))], |c.xs| - 1), searchHistory.visitedStates), stat.SetMaxDepth())
    else
      assert pathHistory.seenStates == searchHistory.visitedStates;
      //  DFS false
      var leftBranch :=
        if c.xs[numSeg].HasExit(false) then
          var leftSucc := c.xs[numSeg].Run(s, false, c.jumpDests);
          //    leftSucc is the successor state of s via false
          if leftSucc in searchHistory.visitedStates then
            //  We have already seen this state, retrieve node that corresponds to this state and
            //  create an edge to it
            assert searchHistory.visitedStates[leftSucc].seg.Some? ==> searchHistory.visitedStates[leftSucc].seg.v < |c.xs|;
            (CFGComputation(BoolCFGraph( [BoolEdge(CFGNode(pathHistory.path, Some(numSeg)), false, searchHistory.visitedStates[leftSucc])]), searchHistory.visitedStates), stat.IncVisited())
          else if leftSucc.EState? && leftSucc.PC() < Int.TWO_256 then
            var nextSeg := PCToSeg(c.xs, leftSucc.PC());
            if nextSeg.Some? then
              var src := CFGNode(pathHistory.path, Some(numSeg));
              var tgt := CFGNode(pathHistory.path + [false], nextSeg);
              var newSeenSegs := pathHistory.seenStates[leftSucc := tgt];
              var newSearchHist := DFSHistory(searchHistory.visitedStates[leftSucc := tgt]);
              var pathHist1 := PathHistory( pathHistory.seen + [tgt], pathHistory.seenPCs + [leftSucc.PC()], pathHistory.path + [false], newSeenSegs);
              var gleft := BuildCFGV6(c, maxDepth - 1, nextSeg.v, leftSucc, pathHist1, newSearchHist, stat);
              (CFGComputation(gleft.0.grph.AddEdge(BoolEdge(src, false, tgt)), gleft.0.states), gleft.1)
            else  //  Next segment could not be found
              (CFGComputation(BoolCFGraph([ BoolEdge(CFGNode(pathHistory.path, Some(numSeg)), false, CFGNode(pathHistory.path + [false])) ]), searchHistory.visitedStates), stat)
          else // left successor of segment resulted in Error state
            (CFGComputation(BoolCFGraph([ BoolEdge(CFGNode(pathHistory.path, Some(numSeg)), false, CFGNode(pathHistory.path + [false])) ]), searchHistory.visitedStates), stat.(errorState := true))
        else // no false exit branch expected for this segment
          (CFGComputation(BoolCFGraph([ ]), searchHistory.visitedStates), stat) ;

      //  The right branch takes into account the states seen in the left branch
      var newVisitedStates := leftBranch.0.VisitedStates() ;
      var leftStats := leftBranch.1;

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
              if rightSucc in newVisitedStates then
                //  We have already seen this state
                assert newVisitedStates[rightSucc].seg.Some? ==> newVisitedStates[rightSucc].seg.v < |c.xs|;
                (CFGComputation(BoolCFGraph( [BoolEdge(CFGNode(pathHistory.path, Some(numSeg)), true, newVisitedStates[rightSucc])]), newVisitedStates), leftStats.IncVisited())
              else if rightSucc.PC() !in pathHistory.seenPCs then
                //  We have not seen this segment.pc before, continue to unfold
                var src := CFGNode(pathHistory.path, Some(numSeg));
                var tgt := CFGNode(pathHistory.path + [true], nextSeg);
                var newSeenSegs := newVisitedStates[rightSucc := tgt];
                var newSearchHist := DFSHistory(newVisitedStates[rightSucc := tgt]);
                var pathHist1 := PathHistory( pathHistory.seen + [tgt], pathHistory.seenPCs + [rightSucc.PC()],pathHistory.path + [true], newSeenSegs);
                var gright := BuildCFGV6(c, maxDepth - 1, nextSeg.v, rightSucc, pathHist1, newSearchHist, leftStats);
                (CFGComputation(gright.0.grph.AddEdge(BoolEdge(src, true, tgt)), gright.0.states), gright.1)
              else
                //  We have seen this PC before. Link to the first CFGNode in the list
                //  with this PC if there is one.
                match SafeLoopFound(c.xs, rightSucc.PC(), pathHistory.seen, pathHistory.path + [true], c.jumpDests) // , pathHistory.path + [true])
                case Some(prev) =>
                  // the computation for this pathHistory.path sopts. We have discovered a
                  //    lasso with the loop part being invariant under
                  //    reachable PCs.
                  assert prev.seg.Some?;
                  assert prev.seg.v < |c.xs|;
                  (CFGComputation(BoolCFGraph([BoolEdge(CFGNode(pathHistory.path, Some(numSeg)), true, prev)], |c.xs|), newVisitedStates), leftStats.IncWpre())
                case None =>
                  //  Progress the DFS with a new node
                  var src := CFGNode(pathHistory.path, Some(numSeg));
                  var tgt := CFGNode(pathHistory.path + [true], nextSeg);
                  var newSeenSegs := newVisitedStates[rightSucc := tgt];
                  var newSearchHist := DFSHistory(newVisitedStates[rightSucc := tgt]);
                  var pathHist1 := PathHistory(pathHistory.seen + [tgt], pathHistory.seenPCs + [rightSucc.PC()], pathHistory.path + [true], newSeenSegs);
                  var gright := BuildCFGV6(c, maxDepth - 1, nextSeg.v, rightSucc, pathHist1, newSearchHist, leftStats);
                  (CFGComputation(gright.0.grph.AddEdge(BoolEdge(src, true, tgt)), gright.0.states), gright.1)
            else // Next segment could not be found
              (CFGComputation(BoolCFGraph([ BoolEdge(CFGNode(pathHistory.path, Some(numSeg)), true, CFGNode(pathHistory.path + [true])) ]), newVisitedStates), leftStats)
          else // right successor of segment resulted in Error state
            (CFGComputation(BoolCFGraph([ BoolEdge(CFGNode(pathHistory.path, Some(numSeg)), true, CFGNode(pathHistory.path + [true])) ]), newVisitedStates), leftStats.(errorState := true))
        else // no true exit
          (CFGComputation(BoolCFGraph([ ], 0), newVisitedStates), leftStats) ;
      (CFGComputation(BoolCFGraph(leftBranch.0.grph.edges + rightBranch.0.grph.edges, |c.xs| - 1), rightBranch.0.states), rightBranch.1)
  }

}

