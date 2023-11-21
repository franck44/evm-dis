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
include "./Minimiser.dfy"
include "./Partition.dfy"
include "./SeqOfSets.dfy"

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
  import Minimiser
  import opened PartitionMod
  import opened SeqOfSets

  const returnColour := "style=filled,color=olivedrab,fontcolor=white,"
  const revertColour := "style=filled,color=orange,fontcolor=white,"
  const invalidColour := "style=filled,color=firebrick,fontcolor=white,"
  const jcolour :="royalblue"
  const skcolour :="black"
  const jumpColour := "color=" + jcolour + ","
  const skipColour := "color=" + skcolour + ","
  const branchColour := "" // style=filled,color=white";
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
      var lab1 := if lab then "<FONT color=\"" + jcolour + "\">jump</FONT>" else "<FONT color=\"" + skcolour + "\">skip</FONT>";
      var labColour := if lab then jumpColour else skipColour;
      "s" + src.ToString() + " -> s" + tgt.ToString() +  " [" + labColour + "label=<" + lab1 + ">]\n"
    }
  }

  /**
    *   A control flow graph with boolean labels/ 
    */
  datatype BoolCFGraph = BoolCFGraph(edges: seq<BoolEdge>, maxSegNum: nat := 0)
  {
    function AddEdge(e: BoolEdge): BoolCFGraph
    {
      BoolCFGraph([e] + edges)
    }

    predicate IsValid()
    {
      && (forall k:: 0 <= k < |edges| ==> edges[k].src.seg.Some? ==> edges[k].src.seg.v <= maxSegNum)
      && (forall k:: 0 <= k < |edges| ==> edges[k].tgt.seg.Some? ==> edges[k].tgt.seg.v <= maxSegNum)
    }

    /**
      *  Convert the list of edges to a map and count the number of states.
      */
    function Minimise(): (g': BoolCFGraph)
      requires this.IsValid()
      ensures g'.IsValid()
      ensures g'.maxSegNum == maxSegNum
    {
      //   assume forall k:: 0 <= k < |edges| ==> edges[k].src.seg.Some? ==> edges[k].src.seg.v < maxSegNum;
      //   assume forall k:: 0 <= k < |edges| ==> edges[k].tgt.seg.Some? ==> edges[k].tgt.seg.v < maxSegNum;
      var r := EdgesToMap(edges, segUpperBound := maxSegNum);
      var idToNum := r.2;
      var numToCFGNode := r.3;
      var lastStateNum := r.0;
      var transitions := r.1;
      assert  forall k:: k in numToCFGNode && numToCFGNode[k].seg.Some? ==> numToCFGNode[k].seg.v <= maxSegNum;

      //   assert forall k:: k in transitions ==> k.0.seg.Some? ==> k.0.seg.v < maxSegNum;
      assert forall i:: 0 <= i <= lastStateNum ==> i in numToCFGNode.Keys;
      //   assert forall k:: k in numToCFGNode.Keys ==> k <= lastStateNum;
      assert forall k:: k in numToCFGNode.Keys  ==> numToCFGNode[k] in idToNum.Keys;
      var a := Auto(lastStateNum + 1, transitions);
      if lastStateNum > 0 then
        var s := set q {:nowarn} | 0 <= q < lastStateNum + 1;
        assert {0} <= s;
        // assume AllNonEmpty([s]);
        // assume DisjointAnyTwo([s]);
        SizeOfNatsUpToNBound(lastStateNum + 1, s);
        assert SetN([s], lastStateNum + 1);
        var p: ValidPartition := Partition(lastStateNum + 1, [s]);
        var p1 := SegNumPartition(p, numToCFGNode, maxSegNum);
        var vp: Minimiser.ValidPair := Minimiser.Pair(a, p1);
        var minim := Minimiser.Minimise(vp);
        assert minim.p.n == vp.p.n == a.numStates;
        //  now recreate a CFGraph
        var listOfEdges := minim.GenerateReduced();
        assert forall k:: 0 <= k < |listOfEdges| ==> listOfEdges[k].0 < minim.p.n && listOfEdges[k].2 < minim.p.n;
        assert forall k:: 0 <= k < |listOfEdges| ==> listOfEdges[k].0 in numToCFGNode && listOfEdges[k].2 in numToCFGNode;

        var x := NatBoolEdgesToCFGEdges(listOfEdges, numToCFGNode, maxSegNum);
        assert forall k:: 0 <= k < |x| ==> x[k].src.seg.Some? ==> x[k].src.seg.v <= maxSegNum;
        assert forall k:: 0 <= k < |x| ==> x[k].tgt.seg.Some? ==> x[k].tgt.seg.v <= maxSegNum;
        var miniCFG := BoolCFGraph(x, maxSegNum);
        assert miniCFG.maxSegNum == maxSegNum;
        miniCFG
      else
        BoolCFGraph([], maxSegNum)
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
    //   var returnColour := "style=filled,color=olivedrab,fontcolor=white,";
    //   var revertColour := "style=filled,color=firebrick,fontcolor=white,";
    //   var branchColour := ""; // style=filled,color=white";

      if |g| > 0 then
        //  check and print src component
        var srctxt :=
          if g[0].src in printed then ""
          else if g[0].src.seg.None? then 
            "s" + g[0].src.ToString() + "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"
          else DOTPrintNodeLabel(g[0].src, xs[g[0].src.seg.v]);
        var tgttxt :=
             if g[0].tgt in printed then ""
          else if g[0].tgt.seg.None? then 
            "s" + g[0].tgt.ToString() + "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"
          else DOTPrintNodeLabel(g[0].tgt, xs[g[0].tgt.seg.v]);
        srctxt + tgttxt + DOTPrintNodes(xs, g[1..], printed + {g[0].src, g[0].tgt})
      else ""
    }

    function DOTPrintNodeLabel(n: CFGNode, s: ValidLinSeg): string
        requires n.seg.Some?
    {
      var lab := DOTSeg2(s, n.seg.v);
      var nodeColour := SegColour(s);
      "s" + n.ToString() + " [" + nodeColour + "label=<\n" + lab + ">]\n"
    }

    /** Print the graph as a DOT digraph */
    function DOTPrint(xs: seq<ValidLinSeg>): string
      requires forall k:: k in this.edges ==> k.src.seg.Some? ==> 0 <= k.src.seg.v < |xs|
      requires forall k:: k in this.edges ==> k.tgt.seg.Some? ==> 0 <= k.tgt.seg.v < |xs|
    {
      var prefix := "digraph CFG {\n node [shape=box]\nnode[fontname=arial]\nedge[fontname=arial]\nranking=TB\n ";
      prefix + DOTPrintNodes(xs) + DOTPrintEdges() + "}\n"
    }
  }

  //    Helpers

  /**
    *   Start with a partition such that every class the same segment number.
    *   @param  n  the max seg number.
    *   @param  p  An initial partition, should be [{0, ... n}]
    */
  function SegNumPartition(p: ValidPartition, m: map<nat, CFGNode>, maxSegNum: nat, n: nat := 0): (p': ValidPartition)
    requires n <= maxSegNum + 1
    requires forall k:: 0 <= k < p.n ==> k in m.Keys
    // requires forall
    ensures p'.n == p.n
    // ensures forall k:: 0 <= k < |p'.elem| ==>
    //     (forall x, x':: x in p'.elem[k] && x' in p'.elem[k] ==>  m[x].seg == m[x'].seg)
    decreases maxSegNum - n

  {   //  there is maxSeg + 1 segments
      // NotEmpty(p);
      // ValidMaxClasses(p);
      // AllClassesInSetU(p);
    if n <= maxSegNum then
      //  split
      var f: nat --> bool := (x: nat) requires 0 <= x < p.n => m[x].seg == Some(n);
      // assert n < |p.elem|;
      var p1 := p.SplitAt(f, |p.elem| - 1);
      // assert  (forall x, x':: x in p.elem[|p.elem| - 1] && x' in p.elem[|p.elem| - 1] ==>  m[x].seg == m[x'].seg);
      // assume forall k:: 0 <= k < p1.n ==> k in m.Keys;
      SegNumPartition(p1, m, maxSegNum, n + 1)
    else
      //  collect states with seg number n
      p

  }

  function {:tailrecursion true} {:timeLimitMultiplier 10} EdgesToMap(edges: seq<BoolEdge>, seenNodes: map<CFGNode, nat> := map[CFGNode([], Some(0)) := 0], reverseSeenNodes: map<nat, CFGNode> := map[0 := CFGNode([], Some(0))] ,builtMap: map<(nat, bool), nat> := map[], lastNum: nat := 0, index: nat := 0, ghost segUpperBound: nat ): (a: (nat, map<(nat, bool), nat>, map<CFGNode, nat>, map<nat, CFGNode>))
    requires index <= |edges|
    // requires forall i, i':: 0 <= i < i' < |edges| ==> edges[i] != edges[i']
    // requires builtMap.Keys == seq q |
    requires forall k:: 0 <= k < |edges| && edges[k].src.seg.Some? ==> edges[k].src.seg.v <= segUpperBound
    requires forall k:: 0 <= k < |edges| && edges[k].tgt.seg.Some? ==> edges[k].tgt.seg.v <= segUpperBound
    requires forall k:: k in builtMap ==> builtMap[k] <= lastNum
    requires forall k: CFGNode {:trigger seenNodes[k]}:: k in seenNodes  ==> seenNodes[k] <= lastNum
    requires forall k:: k in builtMap.Keys ==> k.0 <= lastNum
    requires forall e:: e in edges[..index] ==> e.src in seenNodes
    requires forall e:: e in edges[..index] ==> e.tgt in seenNodes
    requires forall e:: e in edges[..index] ==> (seenNodes[e.src], e.lab) in builtMap.Keys
    requires forall k:: k in reverseSeenNodes.Keys ==> k <= lastNum
    requires forall k:: k in reverseSeenNodes.Keys ==> reverseSeenNodes[k] in seenNodes.Keys
    requires forall n:: 0 <= n <= lastNum ==> n in reverseSeenNodes.Keys
    requires forall k:: k in reverseSeenNodes.Keys ==> reverseSeenNodes[k].seg.Some? ==> reverseSeenNodes[k].seg.v <= segUpperBound
    requires lastNum + 1 >= |reverseSeenNodes|

    // requires forall k:: k in seenNodes <==> k in reverseSeenNodes.Values
    // requires forall k:: k in reverseSeenNodes ==> k in reverseSeenNodes.Values
    // requires forall k:: k in builtMap ==>
    //                       exists src, tgt, lab: bool::
    //                         && src in seenNodes
    //                         && tgt in seenNodes
    //                         && BoolEdge(src, lab, tgt) in edges[..index]
    //                         && seenNodes[src] == k.0
    //                         && lab == k.1
    //                         && seenNodes[tgt] == builtMap[k]

    ensures forall k:: k in a.1 ==> a.1[k] <= a.0
    ensures forall k:: k in a.1.Keys ==> k.0 <= a.0
    ensures forall e:: e in edges ==> e.src in a.2
    ensures forall e:: e in edges ==> e.tgt in a.2
    ensures forall e:: e in edges ==> (a.2[e.src], e.lab) in a.1.Keys

    ensures forall k:: k in a.3.Keys ==> k <= a.0
    ensures forall k:: k in a.3.Keys ==> a.3[k] in a.2.Keys
    ensures forall n:: 0 <= n <= a.0 ==> n in a.3.Keys
    ensures forall k:: k in a.3.Keys ==> a.3[k].seg.Some? ==> a.3[k].seg.v <= segUpperBound
    ensures a.0 + 1 >= |a.3|
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
    if |edges| == index then (lastNum, builtMap, seenNodes, reverseSeenNodes)
    else
      var (src, last, m1, rm1) :=
        if edges[index].src in seenNodes.Keys then
          //   assert edges[index].src in reverseSeenNodes.Values;
          (seenNodes[edges[index].src], lastNum, seenNodes, reverseSeenNodes)
        else (lastNum + 1, lastNum + 1, seenNodes[edges[index].src := lastNum + 1], reverseSeenNodes[lastNum + 1 := edges[index].src]);
      //   assert   edges[index].src in reverseSeenNodes.Values || rm1[lastNum + 1] == edges[index].src ;
      //   assert rm1.Values  >= {edges[index].src};
      //   assert edges[index].src in rm1.Values;
      //   assume forall k:: k in m1 <==> k in rm1.Values;

      var (tgt, last', m2, rm2) :=
        if edges[index].tgt in m1.Keys then
          (m1[edges[index].tgt], last, m1, rm1)
        else (last + 1, last + 1, m1[edges[index].tgt := last + 1], rm1[last + 1 := edges[index].tgt]);
      //   assert  edges[index].tgt in rm1.Values || (last + 1 in rm2.Keys && rm2[last + 1] == edges[index].tgt) ;


      var b := builtMap[(src, edges[index].lab) := tgt];

      //   assume forall k:: k in b ==>
      //                       exists src, tgt, lab: bool::
      //                         && src in m2
      //                         && tgt in m2
      //                         && BoolEdge(src, lab, tgt) in edges[..index + 1 ]
      //                         && m2[src] == k.0
      //                         && lab == k.1
      //                         && m2[tgt] == b[k];
      //   assert edges[index].src in rm2.Values;
      //   assert forall k:: k in m1 ==> k in rm2.Values ;
      EdgesToMap(edges, m2, rm2, b, last', index + 1, segUpperBound)
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
    var prefix := "<B>Segment " + NatToString(numSeg) + " 0x" + Hex.NatToHex(s.StartAddress()) + "</B><BR ALIGN=\"CENTER\"/>\n";
    var body := DOTIns(s.Ins());
    prefix + body
  }

  function SegColour(s: ValidLinSeg): string
  {
    match s
    case STOPSeg(_, _, _) => revertColour
    case RETURNSeg(_, _, _) => returnColour
    case INVALIDSeg(_, _, _) =>  invalidColour
    case JUMPISeg(_, _, _) =>  branchColour
    case _ => ""
  }

  function DOTSeg2(s: ValidLinSeg, numSeg: nat): string
    // requires numSeg < |xs|
  {
    // var s := xs[numSeg];
    var prefix := "<B>Segment " + NatToString(numSeg) + " 0x" + Hex.NatToHex(s.StartAddress()) + "</B><BR ALIGN=\"CENTER\"/>\n";
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

  function NatBoolEdgesToCFGEdges(xs: seq<(nat, bool, nat)>, m: map<nat, CFGNode>, maxSegNum: nat): (r :seq<BoolEdge>)
    requires forall k:: 0 <= k < |xs| ==> xs[k].0 in m && xs[k].2 in m
    requires forall k:: k in m && m[k].seg.Some? ==> m[k].seg.v <= maxSegNum
    ensures forall k:: 0 <= k < |r| && r[k].src.seg.Some? ==> r[k].src.seg.v <= maxSegNum
    ensures forall k:: 0 <= k < |r| && r[k].tgt.seg.Some? ==> r[k].tgt.seg.v <= maxSegNum
  {
    if |xs| == 0 then []
    else
      [BoolEdge(m[xs[0].0], xs[0].1, m[xs[0].2])] + NatBoolEdgesToCFGEdges(xs[1..], m, maxSegNum)
  }

  //   function
  //   function ReverseMap<S, T>(m: map<S, T>): map<T, S>
  //     //   requires forall k, k':: k in m ==> (m[k] == m[k'] ==> k == k')
  //   {
  //     if |m| == 0 then map[]
  //     else map[m[] := ]
  //   }

}