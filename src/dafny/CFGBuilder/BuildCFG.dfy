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
  function BuildCFGV4(xs: seq<ValidLinSeg>, maxDepth: nat, numSeg: nat := 0, s: ValidState := DEFAULT_VALIDSTATE, seen: seq<CFGNode> := [], path: seq<bool> := []): (g: BoolCFGraph)
    requires numSeg < |xs|
    ensures forall k:: k in g.edges ==> k.src.seg.Some? ==> 0 <= k.src.seg.v < |xs|
    ensures forall k:: k in g.edges ==> k.tgt.seg.Some? ==> 0 <= k.tgt.seg.v < |xs|
    decreases maxDepth
  {
    // if numSeg in marked || maxDepth == 0 then ([], marked)
    if maxDepth == 0 then
      BoolCFGraph([])
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
              var gleft := BuildCFGV4(xs, maxDepth - 1, nextSeg.v, leftSucc, seen, path + [false]);
              gleft.AddEdge(BoolEdge(CFGNode(path, Some(numSeg)), false, CFGNode(path + [false], nextSeg)))
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
            if nextSeg.Some? then
              var gright := BuildCFGV4(xs, maxDepth - 1, nextSeg.v, rightSucc, seen, path + [true]);
              gright.AddEdge(BoolEdge(CFGNode(path, Some(numSeg)), true, CFGNode(path + [true], nextSeg)))
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
    decreases |xs| - rank
  {
    if rank == |xs| then None
    else if xs[rank].StartAddress() == pc then Some(rank)
    else PCToSeg(xs, pc, rank + 1)
  }

}

