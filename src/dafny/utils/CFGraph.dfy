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
  // include "./int.dfy"

/** Provide parsing of commadline options. 
  * 
  * Usage: see at the end of the module for an example method.
  */
module CFGraph {

  import opened MiscTypes
  import opened LinSegments
  import opened Instructions
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