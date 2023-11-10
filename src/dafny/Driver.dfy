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
              var r := BuildCFGV4(y, maxDepth) ;
              print "CFG test 1\n";
              print r.DOTPrint(y);
            }

          }

        case Failure(m) =>
      }
    }
  }

  //    Helpers

  /**
    *  Decode a char into a digit.
    */
  function CharToDigit(c: char): (r: Option<nat>)
    // requires '0' <= c < '9'
    ensures r.Some? ==> 0 <= r.v <= 9
  {
    match c
    case '0' => Some(0)
    case '1' => Some(1)
    case '2' => Some(2)
    case '3' => Some(3)
    case '4' => Some(4)
    case '5' => Some(5)
    case '6' => Some(6)
    case '7' => Some(7)
    case '8' => Some(8)
    case '9' => Some(9)
    case _ => None
  }

  predicate IsNatNumber(s: string)
    requires |s| >= 1
    ensures IsNatNumber(s) <==> forall k:: 0 <= k < |s| ==> CharToDigit(s[k]).Some?
  {
    if |s| == 1 then CharToDigit(s[0]).Some?
    else
      match CharToDigit(s[0])
      case Some(v) => IsNatNumber(s[1..])
      case None => false
  }

  function {:tailrecursion false} StringToNat(s: string, lastVal: nat := 0): nat
    requires |s| > 0
    requires IsNatNumber(s)
  {
    if |s| == 1 then CharToDigit(s[0]).v
    else
      var v := CharToDigit(s[|s| - 1]).v;
      //   assert s[..|s| - 1] <= s;
      //   assert |s| >= 2;
      //   assert forall k:: 0 <= k < |s[..|s| - 1]| ==> CharToDigit(s[k]).Some?;
      //   assert IsNatNumber(s[..|s| - 1]);
      v + 10 * StringToNat(s[..|s| - 1])
  }

}

