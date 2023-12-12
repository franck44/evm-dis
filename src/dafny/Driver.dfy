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

include "./disassembler/Disassembler.dfy"
include "./proofobjectbuilder/Splitter.dfy"
include "./proofobjectbuilder/SegmentBuilder.dfy"
include "./proofobjectbuilder/ProofObjectBuilder.dfy"
include "./CFGBuilder/BuildCFG.dfy"
include "./prettyprinters/Pretty.dfy"
include "./utils/ArgParser.dfy"
include "./utils/MiscTypes.dfy"
include "./utils/int.dfy"
include "./utils/Hex.dfy"
include "./utils/EVMObject.dfy"

/**
  *  Provides input reader and write out to stout.
  */
module Driver {

  import opened BinaryDecoder
  import opened Splitter
  import opened PrettyPrinters
  import opened EVMObject
  import opened ArgParser
  import opened BuildCFGraph
  import opened MiscTypes
  import opened State
  import opened Int
  import Hex
  import opened ProofObjectBuilder

  /**
    *  Read the input string
    *  @param  args    
    *  @note   If one arg, this is the string to parse and disassemble.
    *  @note   If two args, first one must be "-d" or "-p" or "-a" to select
    *           the type of outputs.
    */
  method {:verify true} {:timeLimitMultiplier 4} {:main} Main(args: seq<string>)
  {
    var optionParser := new ArgumentParser("<string>");

    //  Register the options and their descriptions
    optionParser.AddOption("-d", "--dis", 0, "Disassemble <string>");
    optionParser.AddOption("-p", "--proof", 0, "Generate proof object for <string>");
    optionParser.AddOption("-s", "--segment", 0, "Print segment of <string>");
    optionParser.AddOption("-l", "--lib", 1, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ");
    optionParser.AddOption("-c", "--cfg", 1, "Max depth. Control flow graph in DOT format");
    optionParser.AddOption("-r", "--raw", 0, "Display non-minimised and minimised CFGs");
    optionParser.AddOption("-f", "--fancy", 0, "Use exit and entry ports in segments do draw arrows.");
    optionParser.AddOption("-n", "--notable", 0, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.");

    if |args| < 2 || args[1] == "--help" {
      print "Not enough arguments\n";
      optionParser.PrintHelp();
    } else if |args| == 2 {
      //  No argument, try to disassemble
      //  Make sure the string is Hexa and has even length
      if |args[1]| % 2 != 0 {
        print "String must have even length, length is ", |args[1]|, "\n";
      } else if Hex.IsHexString(args[1]) {
        var x := Disassemble(args[1]);
        print "Diassembled code:\n";
        PrintInstructions(x);
        print "--------------- Disassembled ---------------------\n";
      } else {
        print "String must be hexadecimal\n";
      }
    } else if args[1] == "--help" || args[1] == "-h" {
      //  Note that this does not work with the dafny run command as --help is a dafny run option
      optionParser.PrintHelp();
    } else {
      // Collect the arguments
      var stringToProcess := args[|args| - 1];
      if |stringToProcess| % 2 != 0 {
        print "String must have even length, length is ", |stringToProcess|, "\n";
      } else if !Hex.IsHexString(stringToProcess) {
        print "String must be hexadecimal\n";
      } else {
        var x := Disassemble(stringToProcess);
        //  Parse arguments
        var optArgs := args[1..|args| - 1];
        // Note: we use an if-then-else as otherwise compileToJava fails
        var disOpt: bool := if optionParser.GetArgs("--dis", optArgs).Success? then true else false;
        var segmentOpt: bool := if optionParser.GetArgs("--segment", optArgs).Success? then true else false;
        var proofOpt: bool := if optionParser.GetArgs("--proof", optArgs).Success? then true else false;
        var libOpt: string :=
          match optionParser.GetArgs("--lib", optArgs)
          case Success(p) => p[0]
          case Failure(_) => "" ;
        var cfgDepthOpt: nat :=
          match optionParser.GetArgs("--cfg", optArgs)
          case Success(args) => if |args[0]| >= 1 && IsNatNumber(args[0]) then StringToNat(args[0]) else 0
          case Failure(_) => 0;
        var rawOpt := if optionParser.GetArgs("--raw", optArgs).Success? then true else false;
        var noTable :=  if optionParser.GetArgs("--notable", optArgs).Success? then true else false;
        var fancy := if optionParser.GetArgs("--fancy", optArgs).Success? then true else false;

        //    Process options
        if disOpt {
          print "Diassembled code:\n";
          PrintInstructions(x);
          print "--------------- Disassembled ---------------------\n";
        }

        var y := SplitUpToTerminal(x, [], []);
        var prog := EVMObj(y);

        if segmentOpt {
          print "Segments:\n";
          PrintSegments(y);
          print "----------------- Segments -------------------\n";
        }

        if proofOpt {
          var z := BuildProofObject(y);
          print "Dafny Proof Object:\n";
          PrintProofObjectToDafny(z, libOpt);
          print "----------------- Proof -------------------\n";
        }

        if cfgDepthOpt > 0 && |y| > 0 && y[0].StartAddress() == 0 {
          print "// maxDepth is:", cfgDepthOpt, "\n";
          //  Build CFG upto depth
          var (g1, stats) := BuildCFGV6(prog, cfgDepthOpt);
          var g := g1.Graph();
          if rawOpt {
            print stats.PrettyPrint();
            print "// Size of CFG: ", g.NumNodes(), " nodes, ", g.NumEdges(), " edges\n";
            print "// Raw CFG\n";
            print g.DOTPrint(y, noTable, fancy);
            print "//----------------- Raw CFG -------------------\n";
          } else {
            //  Minimise
            var g' := g.Minimise();
            expect g'.IsValid();
            assert g'.maxSegNum < |y|;
            var g2 := g.Minimise(true, y);
            print stats.PrettyPrint();
            print "// Size of non-minimised CFG: ", g.NumNodes(), " nodes, ", g.NumEdges(), " edges\n";
            print "// Size of minimised CFG: ", g'.NumNodes(), " nodes, ", g'.NumEdges(), " edges\n";
            print "// Size of equiv-minimised CFG: ", g2.NumNodes(), " nodes, ", g2.NumEdges(), " edges\n";
            print "// Minimised CFG\n";
            print g'.DOTPrint(y, noTable, fancy);
            print "//----------------- Minimised CFG -------------------\n";
          }
        } else {
          if optionParser.GetArgs("--cfg", optArgs).Success? {
            print "No segment found or --cfg argument is 0 or segment 0 does not start at pc=0\n";
          }
        }
      }
    }
  }

}

