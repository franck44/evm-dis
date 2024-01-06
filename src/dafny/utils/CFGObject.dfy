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

include "../utils/MiscTypes.dfy"
include "../utils/LinSegments.dfy"
include "../utils/LinSegments.dfy"
include "../utils/StackElement.dfy"
include "../utils/Automata.dfy"
include "../utils/CFGState.dfy"
include "../utils/EVMObject.dfy"
include "../utils/Statistics.dfy"

/**
  *  Provides proof objects types.
  */
module CFGObject {

  import opened MiscTypes
  import opened LinSegments
  import opened Instructions
  import opened StackElement
  import opened Automata
  import opened CFGState
  import opened EVMObject
  import opened Statistics


  /**
    *  A CFGObj is a tuple (prog, maxDepth, a, minimised, stats) where:
    *  - prog is a valid EVM program
    *  - maxDepth is the maximum depth set to the DFS CFG construction analysis
    *  - a is a valid automata representing the CFG
    *  - minimised is a boolean indicating whether the automata has been minimised or not
    *  - stats is a statistics of the DFS algorithm (maxDepth reached, error states, etc.)
    */
  datatype CFGObj = CFGObj(prog: ValidEVMObj, maxDepth: nat, a: ValidAuto<GState>, minimised: bool, stats: Stats) {

    /**
      * The automaton of this should be bounded
      * This implies that each EGState has a segNum component that is 
      * bounded by the number of segments in the program.
      */
    ghost predicate IsValid() {
      && |prog.xs| >= 1
      && (forall s:: s in a.states ==> s.IsBounded(|prog.xs|))
    }

    /**
      * Print the CFG in dot format and add stats in comments.
      * @param noTable: if true, the HTML labels of the nodes are simplified (no tootips, no table).
      *                 This is useful for large CFGs.
      * @param name: the name of the program.
      */
    method {:print} ToDot(noTable: bool, name: string)
      requires this.IsValid()
    {
      print "/*\n";
      print "maxDepth is:", maxDepth, "\n";
      print stats.PrettyPrint();
      print "# of reachable invalid segments is: ", |ReachableInvalidSegs()|, "\n";
      if !minimised {
        print "Size of CFG: ", a.SSize(), " nodes, ", a.TSize(), " edges\n";
        print "Raw CFG\n";
        print "*/\n";
      } else {
        print "Size of non minimised CFG: ", stats.nonMinimisedSize.0, " nodes, ", stats.nonMinimisedSize.1, " edges\n";
        print "Size of minimised CFG: ", a.SSize(), " nodes, ", a.TSize(), " edges\n";
        print "Minimised CFG\n";
        print "*/\n";
      }

      var wPreOperandsCFG := computeWpre();

      if wPreOperandsCFG.Some? {
        print "// Wpre fixpoint status: ", (if wPreOperandsCFG.v.Left? then "Reached" else "Not reached"), "\n";
      }

      a.ToDot(
        nodeToString := s requires s in a.states => PrintState(s, noTable, wPreOperandsCFG),
        labelToString := (s, l, _) requires s in a.states && 0 <= l => prog.DotLabel(s, l),
        prefix :=
          "graph[labelloc=\"t\", labeljust=\"l\", label=<"
          + MakeTitle(name, a.SSize(),a.TSize(), maxDepth, stats.maxDepthReached)
          + ">]\n"
          + "node [shape=none, fontname=arial, style=\"rounded, filled\", fillcolor= \"whitesmoke\"]\nedge [fontname=arial]\nranking=TB"
      );
      if !minimised {
        print "//----------------- Raw CFG -------------------\n";
      } else {
        print "//----------------- Minimised CFG -------------------\n";
      }
    }

    /**
      *   Compute the Wpre operands fixpoint of the CFG.
      */
    function computeWpre(): (r: Option<Either<seq<nat>, seq<nat>>>)
      requires this.IsValid()
      ensures (r.Some? && r.v.Left? ==> |r.v.l| == |a.states|)
      ensures (r.Some? && r.v.Right? ==> |r.v.r| == |a.states|)
    {
      if prog.HasNoErrorState(a) then
        Some(prog.ComputeWPreOperands(a))
      else
        None
    }

    /**
      *  Helper to extract the Wpre operands from the result of ComputeWPreOperands.
      */
    function ExtractWpre(r: Either<seq<nat>, seq<nat>>): seq<nat>
    {
      match r
      case Left(vv) => vv
      case Right(vv) => vv
    }

    /**
      *  Pretty-print a state.
      *  @param s        The state to print
      *  @param noTable  If true, the HTML labels of the nodes are simplified (no tootips, no table).
      *                  This is useful for large CFGs.
      *  @param wPre     The Wpre operands mapping for the nodes of the CFG.
      *              .   If None, the Wpre is not computed and no information about it is printed 
      *                  in the tooltips.
      */
    function PrintState(s: GState, noTable: bool, wPre: Option<Either<seq<nat>, seq<nat>>>): string
      requires this.IsValid()
      requires wPre == computeWpre()
      requires s in a.states
    {
      if wPre.Some? then
        //  the wpre operands is computed and we can print it
        var wPreValues := ExtractWpre(wPre.v);
        assert |wPreValues| == |a.states|;
        //  Because we have a valid CFGObj, we know that the wpre operands are bounded by the number of states
        //  And as the automaton is valid, indexOf returns a value < |a.states|.
        prog.ToHTML(s, !noTable, Some(wPreValues[a.indexOf[s]]))
      else
        prog.ToHTML(s, !noTable, None)
    }

    /**
      *  Whether the CFG has some reachable states that correspond to invalid segments.
      */
    function ReachableInvalidSegs(): (r: seq<GState>)
      requires this.IsValid()
      ensures forall s:: s in r <==> s in a.states && s.EGState? && s.IsBounded(|prog.xs|) && prog.xs[s.segNum].INVALIDSeg?
    {
      Filter(a.states, (s: GState) requires s in a.states => s.EGState? && s.IsBounded(|prog.xs|) && prog.xs[s.segNum].INVALIDSeg?)
    }

    /**
      * Make a graph label for the CFG including some statistics about the graph.
      */
    function MakeTitle(name: string, numNodes: nat, numEdges: nat, maxDepth: nat, reached: bool): string
    {
      "<B>Program Name: </B> " + name + "<BR ALIGN=\"left\"/>"
      + "<B>Control Flow Graph Info: </B><BR ALIGN=\"left\"/>"
      + "Max depth: " + Int.NatToString(maxDepth) +  " [" + (if reached then "Was reached" else "Was not reached") + "]" + "<BR ALIGN=\"left\"/>"
      + Int.NatToString(numNodes) + " nodes/"
      + Int.NatToString(numEdges) + " edges<BR ALIGN=\"left\"/>"
    }
  }

}

