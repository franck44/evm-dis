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
include "../utils/State.dfy"
include "../utils/CFGState.dfy"
include "../utils/EVMObject.dfy"
include "../utils/Statistics.dfy"
include "../prettyprinters/PrettyInstruction.dfy"
/**
  *  Provides CFG objects & types.
  */
module CFGObject {

  import opened MiscTypes
  import opened LinSegments
  import opened Instructions
  import opened State
  import opened StackElement
  import opened Automata
  import opened CFGState
  import opened EVMObject
  import opened Statistics
  import opened PrettyIns

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

    predicate HasNoErrorState()
    {
      prog.HasNoErrorState(a)
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

      a.ToDot(
        nodeToString := s requires s in a.states => prog.ToHTML(s, !noTable, if s.ErrorGState? then None else Some(|s.st|)),
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

    /**
      * Print the CFG object to Dafny.
      */
    method {:print} ToDafny(name: string := "EVMProofObject", pathToEVMDafny: string := "")
      requires this.IsValid()
      requires this.HasNoErrorState()
    {
      //    optional include of the dafny-EVM files
      if |pathToEVMDafny| > 0 {
        // print "include \"", pathToEVMDafny, "/src/dafny/state.dfy\"", "\n";
        // print "include \"", pathToEVMDafny, "/src/dafny/bytecode.dfy\"", "\n";
        print "\n";
      }

      print "include \"./src/dafny/AbstractSemantics/AbstractSemantics.dfy\"", "\n\n";

      //    Module
      print "module " + name + " {", "\n\n";
      //   print "import opened Int", "\n";
      //   print "import EvmState", "\n";
      //   print "import opened Bytecode", "\n";
      //   print "import ExternalCallLib", "\n";
      print "import opened AbstractSemantics", "\n";
      print "import opened AbstractState", "\n";

      //  build a const with the jumpdests
      //   var j := Map(prog.jumpDests, k => "0x" + Hex.NatToHex(k) + ",");
      /** Set of jumdests. */
      //   var jAsString := if |j| == 0 then "{}" else "{" + Init(Flatten(j)) + "}";
      //   print "/** Set of valid JUMPDESTS for this program. */", "\n";
      //   print "const VALID_JUMPDESTS: set<u256> := " + jAsString + "\n";
      //   print "\n";
      //   print "/** Lemma for Jumpdest */", "\n";
      //   print "lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)", "\n";
      //   print "   ensures forall k:: k in VALID_JUMPDESTS ==> s.IsJumpDest(k)", "\n";

      // Print the transfer functions for each state of the graph.
      PrintProofObjectBody();
      print "}", "\n";
    }

    /**
      * Print the CFG object to Dafny code to verify the CFG.
      */
    method {:print} CFGCheckerToDafny(name: string := "EVMProofObject", pathToEVMDafny: string := "")
      requires this.IsValid()
      requires this.HasNoErrorState()
    {
      //    optional include of the dafny-EVM files
      print "include \"/Users/franck/development/evm-dis/src/dafny/AbstractSemantics/AbstractSemantics.dfy\"", "\n\n";

      //    Module
      print "module " + name + " {", "\n\n";
      print "import opened AbstractSemantics", "\n";
      print "import opened AbstractState", "\n";

      // Print the transfer functions for each state of the graph.
      PrintCFGVerifierBody();
      print "}", "\n";
    }

    /**
      * Iterate over the states of the CFG and print the transfer functions.
      * This proof object is for analysing and reasoning about the program.
      */
    method PrintProofObjectBody(index: nat := 0)
      requires this.IsValid()
      requires this.HasNoErrorState()
      requires index <= |a.states|
      decreases |a.states| - index
    {
      if index < |a.states| {
        // 
        var currentState := a.states[index];
        var startAddress := prog.StartAddress(currentState.segNum);
        print "\n/** Node " , index , "\n";
        print "* Segment Id for this node is: ", currentState.segNum, "\n";
        print "* Starting at 0x", Hex.NatToHex(startAddress),  "\n";
        print "* Segment type is: ", prog.xs[currentState.segNum].SegTypeName(), "\n";
        print "* Minimum stack size for this segment to prevent stack underflow: ", prog.WpOp(currentState.segNum), "\n";
        var minCap := prog.WpCap(currentState.segNum);
        print "* Minimum capacity for this segment to prevent stack overflow: ", minCap, "\n";
        var netStackEffect := prog.StackEffect(currentState.segNum);
        print "* Net Stack Effect: ", (if netStackEffect >= 0 then "+" else ""), netStackEffect , "\n";
        var netCapEffect := prog.CapEffect(currentState.segNum);
        print "* Net Capacity Effect: ", (if netCapEffect >= 0 then "+" else ""), netCapEffect , "\n";
        print "*/\n";
        print "function {:opaque} {:verify false} ExecuteFromCFGNode_s", index, "(s0: EState, gas: nat): (s': EState)\n";
        // print "  // Writes permission for this segment.", "\n";
        // print "  requires s0.WritesPermitted()", "\n";
        print "  // PC requirement for this node.", "\n";
        print "  requires s0.pc == 0x",  Hex.NatToHex(startAddress), " as nat\n";

        //  requirements on the content of the stack at this node
        print "  // Stack requirements for this node.", "\n";
        print "  requires s0.IsValid() \n";
        print "  requires s0.Operands()", (if index ==0 then " == " else " >= "), |currentState.st|, "\n";
        // print "  requires s0.Capacity() >= ", minCap, "\n";
        for k := 0 to |currentState.st| {
          if currentState.st[k].Value? {
            // print "\n  requires s0.Peek(", k, ") == ", "0x" + Hex.NatToHex(currentState.st[k].Extract() as nat), "\n";
            print "\n  requires s0.stack[", k, "] == ", "0x" + Hex.NatToHex(currentState.st[k].Extract() as nat), "\n";
          }
        }
        print "\n";
        print "  decreases gas\n";

        //  Print the code for this segment
        var nodeInstructions := prog.xs[currentState.segNum].ins;
        print "{\n";
        print "if gas == 0 then Revert(s0)", "\n";
        print "else\n";
        // print "  ValidJumpDest(s0);\n";
        PrintInstructionsToDafny(nodeInstructions, EState(startAddress, currentState.st));
        // print "  ValidJumpDest(s", |nodeInstructions|, ");\n";
        // print "  assume s", |nodeInstructions|, ".EXECUTING?", ";\n";
        // print "  assume s", |nodeInstructions|, ".IsJumpDest(s", |nodeInstructions|, ".Peek(0)", ");\n";
        print "   ", PrintInstructionToDafny(prog.xs[currentState.segNum].lastIns, |nodeInstructions|, |nodeInstructions| + 1), "\n";

        // TODO: assert |a.SuccNat(index)| <= 2;
        //  Pretty-print the last state.
        if  |a.SuccNat(index)| == 0 {
          //    the last state is the state returned.
          print "  s", |nodeInstructions| + 1, "\n";
        }
        else if |a.SuccNat(index)| == 1 {
          //    this is either a JUMP or a Next but there is unique successor.
          print "  // jump to the successor Next() or Tgt of JUMP;\n";
          //   print "  assert ExecuteFromCFGNode_s", a.SuccNat(index)[0], ".requires(s", |nodeInstructions|, ");\n";
          //   print "s", |nodeInstructions|, "\n";

          print "  ExecuteFromCFGNode_s", a.SuccNat(index)[0], "(s", |nodeInstructions| + 1, ", gas - 1)\n";

        } else {
          // This must must be two and a JUMPI
          print "  if s", |nodeInstructions|, ".stack[1] > 0 then ";
          //   print "\nassert ExecuteFromCFGNode_s", a.SuccNat(index)[1], ".requires(s", |nodeInstructions|, ");\n";
          //   print "s", |nodeInstructions|, "\n";
          print "\n   ExecuteFromCFGNode_s", a.SuccNat(index)[1], "(s", |nodeInstructions| + 1, ", gas - 1)\n";

          //   print "  else assert ExecuteFromCFGNode_s", a.SuccNat(index)[0], ".requires(s", |nodeInstructions|, ")", ";\n";
          //   print "s", |nodeInstructions|, "\n";
          print "  else", "\n";
          print "     ExecuteFromCFGNode_s", a.SuccNat(index)[0], "(s", |nodeInstructions| + 1, ", gas - 1)", "\n";
        }
        print "}\n";

        PrintProofObjectBody(index + 1);

      }
    }

    /**
      * This proof object is for verifying/validating the CFG.
      */
    method PrintCFGVerifierBody(index: nat := 0)
      requires this.IsValid()
      requires this.HasNoErrorState()
      requires index <= |a.states|
      decreases |a.states| - index
    {
      if index < |a.states| {
        // 
        var currentState := a.states[index];
        var startAddress := prog.StartAddress(currentState.segNum);
        print "\n/** Node " , index , "\n";
        print "* Segment Id for this node is: ", currentState.segNum, "\n";
        print "* Starting at 0x", Hex.NatToHex(startAddress),  "\n";
        print "* Segment type is: ", prog.xs[currentState.segNum].SegTypeName(), "\n";
        print "* Minimum stack size for this segment to prevent stack underflow: ", prog.WpOp(currentState.segNum), "\n";
        var minCap := prog.WpCap(currentState.segNum);
        print "* Minimum capacity for this segment to prevent stack overflow: ", minCap, "\n";
        var netStackEffect := prog.StackEffect(currentState.segNum);
        print "* Net Stack Effect: ", (if netStackEffect >= 0 then "+" else ""), netStackEffect , "\n";
        var netCapEffect := prog.CapEffect(currentState.segNum);
        print "* Net Capacity Effect: ", (if netCapEffect >= 0 then "+" else ""), netCapEffect , "\n";
        print "*/\n";
        print "function {:opaque} {:verify true} ExecuteFromCFGNode_s", index, "(s0: EState, gas: nat): (s': EState)\n";
        print "  // PC requirement for this node.", "\n";
        print "  requires s0.pc == 0x",  Hex.NatToHex(startAddress), " as nat\n";

        //  requirements on the content of the stack at this node
        print "  // Stack requirements for this node.", "\n";
        print "  requires s0.Operands()", (if index ==0 then " >= " else " >= "), |currentState.st|, "\n";
        for k := 0 to |currentState.st| {
          if currentState.st[k].Value? {
            print "\n  requires s0.stack[", k, "] == ", "0x" + Hex.NatToHex(currentState.st[k].Extract() as nat), "\n";
          }
        }
        print "\n";
        print "  decreases gas\n";

        //  Print the code for this segment
        var nodeInstructions := prog.xs[currentState.segNum].ins;
        print "{\n";
        print "if gas == 0 then s0", "\n";
        print "else\n";
        PrintInstructionsToDafny(nodeInstructions, EState(startAddress, currentState.st));
        print "  ", PrintInstructionToDafny(prog.xs[currentState.segNum].lastIns, |nodeInstructions|, |nodeInstructions| + 1), "\n";

        // TODO: assert |a.SuccNat(index)| <= 2;
        //  Pretty-print the last state.
        if  |a.SuccNat(index)| == 0 {
          //    the last state is the state returned.
          print "  // Segment is terminal (Revert, Stop or Return)\n";
          print "  s", |nodeInstructions| + 1, "\n";
        }
        else if |a.SuccNat(index)| == 1 {
          //    this is either a JUMP or a Cont but there is unique successor.
          var commLine := match prog.xs[currentState.segNum]
            case CONTSeg(_, _, _) => "//  Go to the next instruction at pc + 1"
            case JUMPSeg(_, _, _) => "//  JUMP to the target at Peek(0)"
            case _ => "// Segment has one successor but is not a JUMP nor a CONT"
            ;
          print "  ", commLine, "\n";
          print "  ExecuteFromCFGNode_s", a.SuccNat(index)[0], "(s", |nodeInstructions| + 1, ", gas - 1)\n";

        } else {
          // This must must be two and a JUMPI
          print "  // This is a JUMPI segment, determine next pc using second top-most element of stack\n";
          print "  if s", |nodeInstructions|, ".stack[1] > 0 then\n";
          print "   ExecuteFromCFGNode_s", a.SuccNat(index)[1], "(s", |nodeInstructions| + 1, ", gas - 1)\n";
          print "  else\n";
          print "    ExecuteFromCFGNode_s", a.SuccNat(index)[0], "(s", |nodeInstructions| + 1, ", gas - 1)", "\n";
        }
        print "}\n";
        PrintCFGVerifierBody(index + 1);
      }
    }

    /**
      *   Print out a sequence of instructions in the Dafny-EVM format.
      */
    method PrintInstructionsToDafny(xs:seq<ValidInstruction>, currentState: AState, pos: nat := 0)
    {
      if |xs| > 0 {
        var k := PrintInstructionToDafny(xs[0], pos, pos + 1);
        print "  ", k, "\n";
        // var newState := currentState;
        var newState :=
          if currentState.EState? then
            xs[0].NextState(currentState, prog.jumpDests, 0)
          else
            currentState;
        if newState.EState? && pos % 2 == 0 {
          for j := 0 to |newState.stack| {
            if newState.stack[j].Value?  {
              //   print "   assert s", pos + 1, ".Peek(", j, ") == ", "0x" + Hex.NatToHex(newState.stack[j].Extract() as nat), ";\n";
              print "  assert s", pos + 1, ".stack[", j, "] == ", "0x" + Hex.NatToHex(newState.stack[j].Extract() as nat), ";\n";
            }
          }
        }
        PrintInstructionsToDafny(xs[1..], newState, pos + 1);
      }
    }
  }


}

