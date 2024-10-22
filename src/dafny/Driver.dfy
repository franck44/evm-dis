/*
 * Copyright 2024 Franck Cassez
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
include "./prettyprinters/Pretty.dfy"
include "./utils/ArgParser.dfy"
include "./utils/MiscTypes.dfy"
include "./utils/int.dfy"
include "./utils/Hex.dfy"
include "./utils/EVMObject.dfy"
include "./utils/Statistics.dfy"
include "./utils/CFGObject.dfy"
include "./utils/ProofObject.dfy"

/**
  *  Provides input reader and write out to stout.
  */
module Driver {

  import opened BinaryDecoder
  import opened Splitter
  import opened PrettyPrinters
  import opened EVMObject
  import opened ArgParser
  import opened MiscTypes
  import opened Int
  import opened Statistics
  import opened ProofObjectBuilder
  import opened CFGObject
  import opened ProofObject

  /**
    *  Read the input string
    *  @param  args    
    *  @note   If one arg, this is the string to parse and disassemble.
    *  @note   If two args, first one must be "-d" or "-p" or "-a" to select
    *           the type of outputs.
    */
  method {:verify true} {:print} {:timeLimitMultiplier 7} {:main} Main(args: seq<string>)
  {
    var optionParser := new ArgumentParser("<string>");

    //  Register the options and their descriptions
    optionParser.AddOption("-d", "--dis", 0, "Disassemble <string>");
    optionParser.AddOption("-p", "--proof", 0, "Generate proof object to verify the CFG for <string>");
    optionParser.AddOption("-s", "--segment", 0, "Print segment of <string>");
    optionParser.AddOption("-l", "--lib", 1, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ");
    optionParser.AddOption("-c", "--cfg", 1, "Max depth. Control flow graph in DOT format");
    optionParser.AddOption("-r", "--raw", 0, "Display non-minimised and minimised CFGs");
    optionParser.AddOption("-z", "--size", 1, "The max size of segments. Default is upto terminal instructions or JUMPDEST.");
    optionParser.AddOption("-n", "--notable", 0, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.");
    optionParser.AddOption("-t", "--title", 1, "The name of the program.");
    optionParser.AddOption("-i", "--info", 0, "The stats of the program (size, segments).");

    if |args| < 2 || args[1] == "--help" {
      print "Not enough arguments\n";
      optionParser.PrintHelp();
    } else if |args| == 2 {
      //  No argument, try to disassemble
      //  Make sure the string is Hexa and has even length
      if |args[1]| == 0 {
        print "String must be non empty \n";
      } else if |args[1]| % 2 != 0 {
        print "String must be non empty and have even length, length is ", |args[1]|, "\n";
      } else if Hex.IsHexString(if args[1][..2] == "0x" then args[1][2..] else args[1]) {
        assert |args| > 1;
        assert |args[1]| >= 2;
        var x := Disassemble(if args[1][..2] == "0x" then args[1][2..] else args[1]);
        print "Disassembled code:\n";
        PrintInstructions(x);
        print "--------------- Disassembled ---------------------\n";
      } else {
        print "String must be hexadecimal\n";
      }
    } else if args[1] == "--help" || args[1] == "-h" {
      //  Note that this does not work with the dafny run command as --help is a dafny run option
      optionParser.PrintHelp();
    } else {
      assert |args| > 2;
      // Collect the arguments
      var stringToProcess := args[|args| - 1];
      if |stringToProcess| == 0 {
        print "String must be non empty \n";
      } else if |stringToProcess| % 2 != 0 {
        print "String must have even length, length is ", |stringToProcess|, "\n";
      } else if !Hex.IsHexString(if stringToProcess[..2] == "0x" then stringToProcess[2..] else stringToProcess) {
        print "String must be hexadecimal\n";
      } else {
        var x := Disassemble(if stringToProcess[..2] == "0x" then stringToProcess[2..] else stringToProcess);
        // //  Parse arguments
        var optArgs := args[1..|args| - 1];
        // // Note: we use an if-then-else as otherwise compileToJava fails
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
        var info :=  if optionParser.GetArgs("--info", optArgs).Success? then true else false; 
        var maxSegSize :=
          match optionParser.GetArgs("--size", optArgs) 
          case Success(args) =>  if |args[0]| >= 1 && IsNatNumber(args[0]) then Some(StringToNat(args[0])) else None
          case Failure(_) => None;

        var name: string :=
          match optionParser.GetArgs("--title", optArgs)
          case Success(args) => args[0]
          case Failure(_) => "Name not set"; 

        //    Process options
        if disOpt {
          print "Disassembled code:\n";
          PrintInstructions(x);
          print "--------------- Disassembled ---------------------\n";
        }

        var y := SplitUpToTerminal(x, maxSegSize);
        var prog := EVMObj(y);

        if info {
          print "-------- Program Stats ---------\n";
          prog.PrintByteCodeInfo();
          print "-------- End Program Stats ---------\n";
          print "-------- Segment Stats ---------\n";
          prog.PrintSegmentInfo();
          print "-------- End Segment Stats ---------\n";
        }

        if segmentOpt {
          print "Segments:\n";
          PrintSegments(y);
          print "----------------- Segments -------------------\n";
        }

        if proofOpt && cfgDepthOpt == 0 {
          assert forall k:: 0 <= k < |y| ==> y[k].IsValid();
          var z := BuildProofObject(y);
          print "Dafny Proof Object:\n";
          PrintProofObjectToDafny(z, libOpt);
          print "----------------- Proof -------------------\n";
        }

        if cfgDepthOpt > 0 && |y| > 0 && y[0].StartAddress() == 0 {
          var a1, s1 := prog.BuildCFG(maxDepth := cfgDepthOpt, minimise := !rawOpt);
          assert a1.IsValid();
          var cfgObj := CFGObj(prog, cfgDepthOpt, a1, !rawOpt, s1);
          assert cfgObj.IsValid();

          if proofOpt {
            if cfgObj.HasNoErrorState() {
                cfgObj.CFGCheckerToDafny(pathToEVMDafny := libOpt);
            } else {
                print "The CFG has some error states and the Dafny proof object cannot be generated\n";
            }
          } else {
            cfgObj.ToDot(noTable, name);
          }
        }
      }
    }
  }

}

