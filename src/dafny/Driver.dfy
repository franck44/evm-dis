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

    if |args| < 2 {
      print "Not enough arguments\n";
      optionParser.PrintHelp();
    } else {
      //  Parse arguments
      var arguments := optionParser.ParseArgs(args);
      match arguments
      {
        case Success(m) =>
          //  filename should be the last argument
          var fname := args[|args| - 1];
          var x := Disassemble(fname, []);
          if |m.Keys| > 0 {
            if "--dis" in m.Keys {
              PrintInstructions(x);
            }
            if "--proof" in m.Keys {
              var y := SplitUpToTerminal(x, [], []);
              var z := BuildProofObject(y);
              PrintProofObjectToDafny(z, "../evm-dafny/");
            }
            if "--all" in m.Keys {
              PrintInstructions(x);
              var y := SplitUpToTerminal(x, [], []);
              var z := BuildProofObject(y);
              PrintProofObjectToDafny(z, "../evm-dafny/");
            }
          } else {
            //  no recognised arguments. disassemble.
            PrintInstructions(x);
          }

        case Failure(msg) =>
            print msg, "\n";
            optionParser.PrintHelp();
      }
    }
  }

}

