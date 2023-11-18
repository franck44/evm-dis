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
module LoopResolver {

  import opened MiscTypes
  import opened LinSegments
  import opened State
  import opened CFGraph
  import opened WeakPre

  /**
    *   Find the first node in a sequence with a givem value for pc.
    *   @param  xs      The reference segments list.
    *   @param  pc      The pc to find in s.
    *   @param  s       A sequence of CFGNodes.
    *   @param  index   The current index in the search.
    *   @returns        The node, index of the first occurrence of a node in s with 
    *                   segment that has startAddress == pc and None if none. 
    */
  function FindFirstNodeWithPC(xs: seq<ValidLinSeg>, pc: nat, s: seq<CFGNode>, index: nat := 0): (r: Option<(CFGNode, nat)>)
    requires |xs| >= 1
    requires index <= |s|
    requires forall k:: k in s && k.seg.Some? ==> k.seg.v < |xs|

    ensures r.Some? ==> index < |s|
    ensures r.Some? ==> r.v.0.seg.Some? && r.v.0.seg.v < |xs| && xs[r.v.0.seg.v].StartAddress() == pc
    ensures  r.Some? ==>  r.v.1 < |s| && s[r.v.1].seg.Some? && r.v.0.seg.v == s[r.v.1].seg.v

    decreases |s| - index
  {
    if |s| == index then None
    else if s[index].seg.Some? && xs[s[index].seg.v].StartAddress() == pc then Some((s[index], index))
    else FindFirstNodeWithPC(xs, pc, s, index + 1)
  }

  /**
    *   Check if pc has been seen before, and whether we can loop back to an already seen
    *   CFGNode on this path.
    *
    *   @note   The seenOnPath has all the nodes seen before the current one.
    *           The current one has startAddress == pc.
    *   @todo   Fix this as it does not compute the correct result.
    *           Need to include resursion on the path in WPreSeqSegs.
    */
  function SafeLoopFound(xs: seq<ValidLinSeg>, pc: nat, seenOnPath: seq<CFGNode>): (r: Option<CFGNode>)
    requires |xs| >= 1
    requires pc < Int.TWO_256
    requires 0 < |seenOnPath| // == |path|
    requires forall k:: k in seenOnPath ==> k.seg.Some? && k.seg.v < |xs|
    requires xs[seenOnPath[|seenOnPath| - 1].seg.v].JUMPSeg? || xs[seenOnPath[|seenOnPath| - 1].seg.v].JUMPISeg?
    ensures r.Some? ==> r.v.seg.Some? && r.v.seg.v < |xs|
    decreases |seenOnPath|
  {
    match FindFirstNodeWithPC(xs, pc, seenOnPath)
    case Some(v) =>
      //  some properties must hold on the path defined by the index v.1
      var init := seenOnPath[v.1];
      //  the CFGMNode at index v.1 has a segment with start address == pc
      assert xs[init.seg.v].StartAddress() == pc;
      //  get the path false|true that led from init to last node
      var path := seenOnPath[v.1..];
      //  compute the list of segments defined by the nodes in path
      var segs := NodesToSeg(path);
      //  compute the Wpre for last node path to lead to pc (via true)
      assert pc < Int.TWO_256;
      var tgtCond := xs[seenOnPath[|seenOnPath| - 1].seg.v].LeadsTo(pc);
      //    Compute the WPre for for segments in path
      var w1 := WPreSeqSegs(segs, tgtCond, xs, pc);
      if w1.StTrue? then
        Some(v.0)
      else
      //  Try a potential second occurrence of pc om seenOnPath
      if 0 < |seenOnPath[v.1..|seenOnPath|]| < |seenOnPath| then
        SafeLoopFound(xs, pc, seenOnPath[v.1..|seenOnPath|])
      else None

    case None => None
  }

  //   lemma {:axiom} foo()

  /**
    *   Convert a sequence of CFGNodes into the sequence of segments they correspond to.
    *   @param  xn      The seq of CFGNodes
    *   @param  xs      A list of known segments.
    *   @returns        The list of segments defined by xn.
    */
  function {:tailrecursion true} NodesToSeg(xn: seq<CFGNode>): (s: seq<nat>)
    requires forall k:: k in xn ==> k.seg.Some? 
    ensures |xn| == |s|
    ensures forall i:: 0 <= i < |s| ==> s[i] == xn[i].seg.v
  {
    if |xn| == 0 then []
    else
      [xn[0].seg.v] + NodesToSeg(xn[1..])
  }

}

