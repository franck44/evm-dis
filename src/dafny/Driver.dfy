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
include "./prettyprinters/Pretty.dfy"
include "./utils/ArgParser.dfy"
  /**
    *  Provides input reader and write out to stout.
    */
module Driver {

  import opened BinaryDecoder
  import opened Splitter
  import opened PrettyPrinters
  import opened ProofObjectBuilder
  import opened ArgParser

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
    var optionParser := new ArgumentParser("<filename>");

    //  Register the options
    optionParser.AddOption("-d", "--dis", 0, "Disassemble <filename>");
    optionParser.AddOption("-p", "--proof", 0, "Generate proof object for <filename>");
    optionParser.AddOption("-a", "--all", 0, "Same as -d -p");
    optionParser.AddOption("-l", "--lib", 1, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ");

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
    }
  }

}

