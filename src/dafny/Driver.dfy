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

// include "./utils/EVMOpcodes.dfy"
include "./disassembler/Disassembler.dfy"
  // include "../utils/Hex.dfy"

/**
  *  Provides input reader and write out to stout.
  */
module Driver {


  import opened BinaryDecoder
  import opened EVMOpcodes

  /**
    *  Read the input string
    */
  method {:verify true} {:main} Main(args: seq<string>)
  {
    if |args| < 2 {
      print "Expected 1 arguments, got ", |args| - 1, "\n";
    } else {
      var x := Disassemble(args[1], []);
      PrintInstructions(x);
      print "OK0", "\n";
    }
  }

  /**
    *  Print disassembled code to stdout.
    */
  method {:tailrec} PrintInstructions(s: seq<Instruction>)
  {
    if |s| == 0 {
      print "OK1", "\n";
    } else {
      print s[0].ToString(), "\n";
      PrintInstructions (s[1..]);
    }
  }

}

