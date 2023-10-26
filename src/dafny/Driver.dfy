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

/**
  *  Provides input reader and write out to stout.
  */
module Driver {

  import opened BinaryDecoder
  import opened Splitter
  import opened PrettyPrinters
  import opened ProofObjectBuilder

  const usageMsg := "Usage: \n -d <string> or <string>: disassemble <string>\n -p <string>: Proof object\n -a: both -d and -p"

  /**
    *  Read the input string
    *   @param  args    
    *   @note   If one arg, this is the string to parse and disassemble.
    *   @note   If two args, first one must be "-d" or "-p" or "-a" to select
    *           the type of outputs.
    */
  method {:verify true} {:main} Main(args: seq<string>)
  {
    if |args| < 2 {
      print "Not enough arguments\n";
      print usageMsg, "\n";
    } else if |args| == 2 {
      //  Disassemble
      print "Disassembling code", "\n";
      var x := Disassemble(args[1], []);
      PrintInstructions(x);
    } else {
      assert |args| >= 3;
      match args[1]
      case "-d" =>
        //  Disassemble
        print "Disassembling code", "\n";
        var x := Disassemble(args[2], []);
        PrintInstructions(x);

      case "-p" =>
        //  Disassemble and compute proof object
        var x := Disassemble(args[2], []);
        var y := SplitUpToTerminal(x, [], []);
        var z := BuildProofObject(y);
        PrintProofObjectToDafny(z);

      case "-a" =>
        var x := Disassemble(args[2], []);
        PrintInstructions(x);
        var y := SplitUpToTerminal(x, [], []);
        var z := BuildProofObject(y);
        PrintProofObjectToDafny(z);

      case _ =>
        print "Cannot parse arguments ", args[1], "\n";
        print usageMsg, "\n";    }
  }

}

