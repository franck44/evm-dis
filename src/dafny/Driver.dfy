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
  /**
    *  Provides input reader and write out to stout.
    */
module Driver {

  import opened BinaryDecoder
  import opened Splitter
  import opened PrettyPrinters
  import opened ProofObjectBuilder
  import opened ArgParser
  import opened BuildCFGraph
  import opened MiscTypes
  import opened State
  import opened Int

  //   const usageMsg := "Usage: \n -d <string> or <string>: disassemble <string>\n -p <string>: Proof object\n -a: both -d and -p"



  /**
    *  Read the input string
    *   @param  args    
    *   @note   If one arg, this is the string to parse and disassemble.
    *   @note   If two args, first one must be "-d" or "-p" or "-a" to select
    *           the type of outputs.
    */
  method {:verify true} {:main} Main(args: seq<string>)
  {
    var optionParser := new ArgumentParser("<string>");

    //  Register the options
    optionParser.AddOption("-d", "--dis", 0, "Disassemble <string>");
    optionParser.AddOption("-p", "--proof", 0, "Generate proof object for <string>");
    optionParser.AddOption("-s", "--segment", 0, "Print segment of <string>");
    optionParser.AddOption("-a", "--all", 0, "Same as -d -p");
    optionParser.AddOption("-l", "--lib", 1, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ");
    optionParser.AddOption("-c", "--cfg", 1, "Max depth. Control flow graph in DOT format");
    optionParser.AddOption("-r", "--raw", 1, "Display non-minimised and minimised CFGs");
    optionParser.AddOption("-f", "--fancy", 0, "Use exit and entry ports in segments do draw arrows (apply minimised only).");
    optionParser.AddOption("-n", "--notable", 0, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.");

    if |args| < 2 || args[1] == "--help" {
      print "Not enough arguments\n";
      optionParser.PrintHelp();
    } else if |args| == 2 {
      //  Disassemble
      var x := Disassemble(args[1], []);
      PrintInstructions(x);
    } else if args[1] == "--help" || args[1] == "-h" {
      //  Note that this does not work with the dafny run command as --help is a dafny run option
      optionParser.PrintHelp();
    } else {

      var stringToProcess := args[|args| - 1];
      var optArgs := args[1..|args| - 1];
      var x := Disassemble(stringToProcess, []);
      //  Parse arguments
      match optionParser.GetArgs("--dis", optArgs) {
        case Success(_) => PrintInstructions(x);
        case Failure(m) =>
      }

      match optionParser.GetArgs("--segment", optArgs) {
        case Success(_) =>
          print "Segments:\n";
          var y := SplitUpToTerminal(x, [], []);
          PrintSegments(y);
        case Failure(m) =>
      }

      match optionParser.GetArgs("--proof", optArgs) {
        case Success(_) =>
          var pathToDafnyLib := 
            (match optionParser.GetArgs("--lib", optArgs)
             case Success(p) => p[0]
             case Failure(_) => "") ;
          var y := SplitUpToTerminal(x, [], []);
          var z := BuildProofObject(y);
          PrintProofObjectToDafny(z, pathToDafnyLib);
        case Failure(m) =>
      }

      match optionParser.GetArgs("--all", optArgs) {
        case Success(_) =>
          PrintInstructions(x);
          var pathToDafnyLib :=
            (match optionParser.GetArgs("--lib", optArgs)
             case Success(p) => p[0]
             case Failure(_) => "") ;
          var y := SplitUpToTerminal(x, [], []);
          var z := BuildProofObject(y); 
          PrintProofObjectToDafny(z, pathToDafnyLib);
        case Failure(m) =>
      } 

      match optionParser.GetArgs("--cfg", optArgs) {
        case Success(m) =>
          print "CFG:\n";
          var y := SplitUpToTerminal(x, [], []);
          if |y| == 0 {
            print "No segment found\n";
          } else if |m[0]| == 0 || !IsNatNumber(m[0]) {
            print "Argument to --cfg is not a nat.\n";
          } else {
            var maxDepth := StringToNat(m[0]);
            print "maxDepth is:", maxDepth, "\n";
            var startAddress := y[0].StartAddress();
            var startState := DEFAULT_VALIDSTATE.(pc := startAddress);
            if y[0].StartAddress() != 0 {
              print "Segment 0 does not start at address 0.\n";
            } else {
              var jumpDests := CollectJumpDests(y);
              //  Use interndiary g1 as otherwise Java compile does not work.
              var g1 := BuildCFGV5(y, maxDepth, jumpDests);
              var g := g1.0;
              if optionParser.GetArgs("--raw", optArgs).Success? {
                print "Size of CFG: ", |g1.1|, " nodes, ", |g.edges|, "edges\n";
                print "Raw CFG\n";
                print g.DOTPrint(y);
              } else {
                var fancy := optionParser.GetArgs("--fancy", optArgs).Success?;
                var simple :=  if optionParser.GetArgs("--notable", optArgs).Success? then true else false;
                print "Computing Minimised CFG\n";
                var g' := g.Minimise();
                expect g'.IsValid();
                assert g'.maxSegNum < |y|;
                print "Size of minimised CFG: ", g'.numNodes(), " nodes, ", g'.numEdges(), " edges\n";
                print "Minimised CFG\n";
                print g'.DOTPrint(y, simple, fancy);
              }
            }
          }
        case Failure(m) =>
      }
    }
  } 

}

