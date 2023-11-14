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

include "./MiscTypes.dfy"
include "./LinSegments.dfy"
include "./Automata.dfy"

/** Provide parsing of commadline options. 
  * 
  * Usage: see at the end of the module for an example method.
  */
module CFGraph {

  import opened MiscTypes
  import opened LinSegments
  import opened Instructions
  import opened Automata
  import opened Int

  /**
    *   A node.
    */
  datatype CFGNode = CFGNode(id: seq<bool>, seg: Option<nat> := None)
  {
    function ToString(): string
    {
      BoolsToString(id)
    }
  }

  /**
    *   An dedge with a boolean label.
    */
  datatype BoolEdge = BoolEdge(src: CFGNode, lab: bool, tgt: CFGNode)
  {
    /** Print to DOT format. */
    function DOTPrint(): string
    {
      var lab := if lab then "true" else "false";
      "s" + src.ToString() + " -> s" + tgt.ToString() +  " [label=" + lab + "]\n"
    }
  }

  /**
    *   A control flow graph with boolean labels/ 
    */
  datatype BoolCFGraph = BoolCFGraph(edges: seq<BoolEdge>)
  {
    function AddEdge(e: BoolEdge): BoolCFGraph
    {
      BoolCFGraph([e] + edges)
    }

    /**
      *  Convert the list of edges to a map and count the number of states.
      */
    // function ToAutomata(): ValidAuto
    // {

    // }

    /** Print to edges DOT format. */
    function DOTPrintEdges(xe: seq<BoolEdge> := edges): string
    {
      if |xe| > 0 then xe[0].DOTPrint() + DOTPrintEdges(xe[1..])
      else ""
    }

    /** Print to edges DOT format. */
    function DOTPrintNodes(xs: seq<ValidLinSeg>, g: seq<BoolEdge> := edges, printed: set<CFGNode> := {}): string
      requires forall k:: k in g ==> k.src.seg.Some? ==> 0 <= k.src.seg.v < |xs|
      requires forall k:: k in g ==> k.tgt.seg.Some? ==> 0 <= k.tgt.seg.v < |xs|
    {
      if |g| > 0 then
        //  check and print src component
        var srctxt :=
          if g[0].src !in printed then
            var numSeg := g[0].src.seg;
            var lab := if numSeg.Some? then DOTSeg(xs, numSeg.v) else "ErrorEnd <BR ALIGN=\"CENTER\"/>\n";
            "s" + g[0].src.ToString() + " [label=<\n" + lab + ">]\n"
          else "";
        var tgttxt :=
          if g[0].tgt !in printed && g[0].src != g[0].tgt then
            var numSeg := g[0].tgt.seg;
            var lab := if numSeg.Some? then DOTSeg(xs, numSeg.v) else "ErrorEnd <BR ALIGN=\"CENTER\"/>\n";
            "s" + g[0].tgt.ToString() + " [label=<\n" + lab + ">]\n"
          else "";
        srctxt + tgttxt + DOTPrintNodes(xs, g[1..], printed + {g[0].src, g[0].tgt})
      else ""
    }

    /** Print the graph as a DOT digraph */
    function DOTPrint(xs: seq<ValidLinSeg>): string
      requires forall k:: k in this.edges ==> k.src.seg.Some? ==> 0 <= k.src.seg.v < |xs|
      requires forall k:: k in this.edges ==> k.tgt.seg.Some? ==> 0 <= k.tgt.seg.v < |xs|
    {
      var prefix := "digraph CFG {\n node [shape=box]\nranking=TB\n ";
      prefix + DOTPrintNodes(xs) + DOTPrintEdges() + "}\n"
    }
  }

  //    Helpers

  function {:tailrecursion true} {:timeLimitMultiplier 10} EdgesToMap(edges: seq<BoolEdge>, seenNodes: map<CFGNode, nat> := map[CFGNode([], Some(0)) := 0], builtMap: map<(nat, bool), nat> := map[], lastNum: nat := 0, index: nat := 0): (a: (nat, map<(nat, bool), nat>, map<CFGNode, nat>))
    requires index <= |edges|
    requires forall k:: k in builtMap ==> builtMap[k] <= lastNum
    requires forall k: CFGNode {:trigger seenNodes[k]}:: k in seenNodes  ==> seenNodes[k] <= lastNum
    requires forall k:: k in builtMap.Keys ==> k.0 <= lastNum
    requires forall e:: e in edges[..index] ==> e.src in seenNodes
    requires forall e:: e in edges[..index] ==> e.tgt in seenNodes
    requires forall e:: e in edges[..index] ==> (seenNodes[e.src], e.lab) in builtMap.Keys
    // requires forall k:: k in builtMap ==>
    //                       exists src, tgt, lab: bool::
    //                         && src in seenNodes
    //                         && tgt in seenNodes
    //                         && BoolEdge(src, lab, tgt) in edges[..index]
    //                         && seenNodes[src] == k.0
    //                         && lab == k.1
    //                         && seenNodes[tgt] == builtMap[k]

    ensures forall k:: k in a.1.Values ==> k <= a.0
    ensures forall k:: k in a.1.Keys ==> k.0 <= a.0
    ensures forall e:: e in edges ==> e.src in a.2
    ensures forall e:: e in edges ==> e.tgt in a.2
    ensures forall e:: e in edges ==> (a.2[e.src], e.lab) in a.1.Keys
    // ensures forall k:: k in a.1 ==>
    //                      exists src, tgt, lab: bool::
    //                        && src in a.2
    //                        && tgt in a.2
    //                        && BoolEdge(src, lab, tgt) in edges
    //                        && a.2[src] == k.0
    //                        && lab == k.1
    //                        && a.2[tgt] == a.1[k]

    decreases |edges| - index
  {
    if |edges| == index then (lastNum, builtMap, seenNodes)
    else
      var (src, last, m1) :=
        if edges[index].src in seenNodes.Keys then
          (seenNodes[edges[index].src], lastNum, seenNodes)
        else (lastNum + 1, lastNum + 1, seenNodes[edges[index].src := lastNum + 1]);
      var (tgt, last', m2) :=
        if edges[index].tgt in m1.Keys then
          (m1[edges[index].tgt], last, m1)
        else (last + 1, last + 1, m1[edges[index].tgt := last + 1]);
      var b := builtMap[(src, edges[index].lab) := tgt];

    //   assume forall k:: k in b ==>
    //                       exists src, tgt, lab: bool::
    //                         && src in m2
    //                         && tgt in m2
    //                         && BoolEdge(src, lab, tgt) in edges[..index + 1 ]
    //                         && m2[src] == k.0
    //                         && lab == k.1
    //                         && m2[tgt] == b[k];
      EdgesToMap(edges, m2, b, last', index + 1)
      //   EdgesToMap(edges, m2, builtMap + map[(src, edges[index].lab) := tgt], last', index + 1)
  }

  function BoolsToString(x: seq<bool>): string
  {
    if |x| == 0 then "E"
    else
      [if x[0] then '1' else '0'] + BoolsToString(x[1..])
  }

  function DOTSeg(xs: seq<ValidLinSeg>, numSeg: nat): string
    requires numSeg < |xs|
  {
    var s := xs[numSeg];
    var prefix := "Segment " + NatToString(numSeg) + " 0x" + Hex.NatToHex(s.StartAddress()) + "<BR ALIGN=\"CENTER\"/>\n";
    var body := DOTIns(s.Ins());
    prefix + body
  }

  function {:tailrecursion true} DOTIns(xi: seq<ValidInstruction>): string
  {
    if |xi| == 0 then ""
    else
      var a := xi[0].ToString() + " <BR ALIGN=\"LEFT\"/>\n";
      a + DOTIns(xi[1..])
  }

}