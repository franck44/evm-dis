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

  /**
    *   Not used but useful to debug.
    */
  method {:tailrec} PrintSegments(xs: seq<LinSeg>, num: nat := 0)
  {
    if |xs| > 0 {
      //
      print "Segment ", num, "\n";
      var k := xs[0].WeakestPreOperands(0);
      var l := xs[0].WeakestPreCapacity(0);
      if xs[0].JUMPSeg? || xs[0].JUMPISeg? {
        //  Print the stack tracker value
        print "JUMP/JUMPI: ", SegBuilder.JUMPResolver(xs[0]), "\n";
      }
      print "WeakestPre Operands:", k, "\n";
      print "WeakestPre Capacity:", l, "\n";
      PrintInstructions(xs[0].Ins());
      PrintSegments (xs[1..], num + 1);
    }
  }

  //    Helpers

  /** Collect the JUMPDEST addresses in proof objects. */
  function {:tailrecursion true} CollectJumpDest(xs: seq<ProofObj>): seq<nat> {
    if |xs| == 0 then []
    else xs[0].CollectJumpDest() + CollectJumpDest(xs[1..])
  }


  /** Collect the JUMPDEST addresses as hex strings in proof objects. */
  function {:tailrecursion true} CollectJumpDestAsString(xs: seq<nat>): string {
    if |xs| == 0 then []
    else " ensures s.IsJumpDest(0x" + NatToHex(xs[0]) + " as u256)\n" + CollectJumpDestAsString(xs[1..])
  }

  /**
    *   Print out each linear segment as a Dafny function.
    *   Instructions are the Dafny-EVM instructions.
    */
  method {:tailrec} PrintProofObjectToDafny(xs: seq<ProofObj>, num: nat := 0)
  {
    // Print validJumpDests lemma
    var j := CollectJumpDestAsString(CollectJumpDest(xs));
    if |j| > 0 && num == 0 {
      print "/** Lemma for Jumpdest */", "\n";
      print "lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)", "\n";
      print j;
      print "\n";
    }

    if |xs| > 0 {
      // 
      var startAddress := NatToHex(xs[0].s.Ins()[0].address);
      print "\n/** Code starting at 0x", startAddress,  " */\n";
      print "function {:opaque} ExecuteFromTag_", num, "(s0: EvmState.ExecutingState): (s': EvmState.State)\n";
      print "  requires s0.PC() == 0x", startAddress, " as nat\n";
      print "  requires s0.Operands() >= ";
      if xs[0].wpOp.None? {
        print "???" ;
      } else {
        print xs[0].wpOp.Extract();
      }
      print "\n";
      print "  requires s0.Capacity() >= ";
      if xs[0].wpCap.None? {
        print  "???";
      } else {
        print xs[0].wpCap.Extract();
      }
      print "\n";
      //    If jump and target of jump is known print it.
      if xs[0].JUMP? && xs[0].s.lastIns.op.IsJump() {
        { match xs[0].tgt
          case Right(v) =>
            print "  requires s0.IsJumpDest(s0.Peek(", v, "))\n";
          case _ => print ""  ;
        }
      }

      //    If jump and target of jump is known print it.
      if xs[0].JUMP? && xs[0].s.lastIns.op.IsJump() {
        print "  ensures s'.EXECUTING?\n";
        print "  ensures s'.PC() ==  ";
        { match xs[0].tgt
          case Left(xc) => print "0x", xc;
          case Right(v) =>
            print "s0.Peek(", v, ") as nat";
        }
        //  If JUMPI PC could be either tgt or instruction after last.
        if xs[0].s.lastIns.op.opcode == JUMPI {
          print " || s'.PC() == 0x", NatToHex(xs[0].s.lastIns.address + 1);
        }
        print "\n";

        //    Print the constraint for the net stack size effect
        var n := xs[0].StackEffect();
        print "  ensures s'.Operands() == s0.Operands()";
        if n >= 0 {
          print " + ", n;
        } else {
          print " - ", -n;
        }
        print "\n";
      }

      print "{\n";
      print "  ValidJumpDest(s0);\n";
      PrintInstructionsToDafny(xs[0].s.Ins());
      //    Return last state
      print "  s", |xs[0].s.Ins()|, "\n";
      print "}\n";
      PrintProofObjectToDafny(xs[1..], num + 1);
    }
  }

  /**
    *   Print out a sequence of instructions in the Dafny-EVM format.
    */
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

