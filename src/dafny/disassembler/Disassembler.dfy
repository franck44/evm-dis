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
include "./OpcodeDecoder.dfy"
include "../utils/Hex.dfy"

/**
  *  Provides binary decoder.
  */
module BinaryDecoder {

  datatype Option<T> = None | Some(v: T)

  import opened OpcodeDecoder
  import opened EVMOpcodes
  import opened Hex

  /**
    *  Read the input string
    */
  //   method {:verify false} {:main} Main(args: seq<string>) {
  //     if |args| < 2 {
  //       print "Expected 1 arguments, got ", |args| - 1, "\n";
  //     } else {
  //       var x := Dis(args[1], []);
  //       Print(InsToLines(x, []));
  //       print "OK0", "\n";
  //     }
  //   }

  //   method {:tailrec} Print(s: seq<string>)
  //   {
  //     if |s| == 0 {
  //       print "OK1", "\n";
  //     } else {
  //       print s[0], "\n";
  //       Print (s[1..]);
  //     }
  //   }

  /**
    *  Disassemble a string into a sequence of instructions.
    */
  function {:tailrec} Disassemble(s: string, p: seq<Instruction> := []): seq<Instruction>
    decreases |s|
  {
    if |s| == 0 then
      p
    else if |s| == 1 then
      p + [Instruction(Decode(INVALID))]
    else
      assert |s| >= 2;
      // Try to decode next instruction
      match HexToU8(s[..2])
      case None => p + [Instruction(Decode(INVALID))]
      case Some(v) =>
        //  Try to read parameters of opcode
        var op := Decode(v);
        if op.Args() > 0 then
          //  try to skip 2 * Args()
          if |s[2..]| < 2 * op.Args() then
            p + [Instruction(Decode(INVALID))]
          else
            assert |s[2..][2 * op.Args()..]| < |s|;
            Disassemble(s[2..][2 * op.Args()..], p + [Instruction(op, s[2..][..2 * op.Args()])])
        else
          Disassemble(s[2..], p + [Instruction(op)])
  }

// function Disassemble(s: string): (code: seq<Instruction>)
// {
//     DisassembleHelper(s, [])
// }
  
}

