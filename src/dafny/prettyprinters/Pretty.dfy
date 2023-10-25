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

include "../utils/Hex.dfy"
include "../utils/Instructions.dfy"
include "../utils/LinSegments.dfy"
include "../utils/ProofObject.dfy"
include "../proofobjectbuilder/SegmentBuilder.dfy"
include "../utils/OpcodesConstants.dfy"
include "./PrettyInstruction.dfy"
/**
  *  Provides pretty printers.
  */
module PrettyPrinters {

  import opened EVMOpcodes
  import opened Hex
  import opened Int
  import opened Instructions
  import opened LinSegments
  import SegBuilder
  import opened ProofObject
  import opened EVMConstants
  import opened PrettyIns

  /**
    *  Print disassembled code to stdout.
    */
  method {:tailrec} PrintInstructions(s: seq<Instruction>)
  {
    if |s| > 0 {
      //  The addresses should fit within TWO_32, otherwise there is a problem.
      var formattedAddress := if s[0].address < Int.TWO_32 then Hex.U32ToHex(s[0].address as Int.u32) else "OutofRange";
      print formattedAddress, ": ", s[0].ToString(), "\n";
      PrintInstructions (s[1..]);
    }
  }

  method {:tailrec} PrintSegments(xs: seq<LinSeg>, num: nat := 0)
  {
    if |xs| > 0 {
      // 
      print "Segment ", num, "\n";
      //   var k := xs[0].WeakestPreOperands(0);
      //   var l := xs[0].WeakestPreCapacity(0);
      //   if xs[0].JUMPSeg? || xs[0].JUMPISeg? {
      //     //  Print the stack tracker value
      //     print "JUMP/JUMPI: ", SegBuilder.JUMPResolver(xs[0]), "\n";
      //   }
      //   print "WeakestPre Operands:", k, "\n";
      //   print "WeakestPre Capacity:", l, "\n";
      PrintInstructions(xs[0].Ins());
      PrintSegments (xs[1..], num + 1);
    }
  }

  method {:tailrec} PrintProofObject(xs: seq<ProofObj>, num: nat := 0)
  {
    if |xs| > 0 {
      // 
      print "Proof Object ", num, "\n";
      print "WeakestPre Operands:", xs[0].wpOp, "\n";
      print "WeakestPre Capacity:", xs[0].wpCap, "\n";
      if xs[0].JUMP? {
        //  Print the stack tracker value
        print "JUMP/JUMPI: ", xs[0].tgt, "\n";
      }

      PrintInstructions(xs[0].s.Ins());
      PrintProofObject(xs[1..], num + 1);
    }
  }

  method {:tailrec} PrintProofObjectToDafny(xs: seq<ProofObj>, num: nat := 0)
  {
    if |xs| > 0 {
      // 
      var startAddress := NatToHex(xs[0].s.Ins()[0].address);
      print "\n/** Code staring at 0x", startAddress,  " */\n";
      print "function ExecuteFromTag_", num, "(s0: EvmState.ExecutingState): (s': EvmState.State)\n";
      print "  requires s0.PC() == 0x", startAddress, " as nat\n";
      print "  requires s0.Operands() >= ", xs[0].wpOp, "\n";
      print "  requires s0.Capacity() >= ", xs[0].wpCap, "\n";

      print "  ensures s'.EXECUTING?\n";
      print "{\n";
        PrintInstructionsToDafny(xs[0].s.Ins());
      print "}\n";
      PrintProofObjectToDafny(xs[1..], num + 1);
    }
  }

  method PrintInstructionsToDafny(xs:seq<Instruction>, pos: nat := 0)
  {
    // PrintInstructions(xs);
    if |xs| > 0 {
        var k := PrintInstructionToDafny(xs[0], pos, pos + 1);
        print "  ", k, "\n";
        PrintInstructionsToDafny(xs[1..], pos + 1);
    } 
  }

    

}

