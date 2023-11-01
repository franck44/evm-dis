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
  method {:tailrec} PrintSegments(xs: seq<ValidLinSeg>, num: nat := 0)
  {
    assert forall i:: 0 <= i < |xs| ==>
                        (forall k:: 0 <= k < |xs[i].Ins()| ==> xs[i].Ins()[k].op.IsValid());
    if |xs| > 0 {
      //
      print "Segment ", num, "\n";
      var k := xs[0].WeakestPreOperands(0);
      var l := xs[0].WeakestPreCapacity(0);
      if xs[0].JUMPSeg? || xs[0].JUMPISeg? {
        //  Print the stack tracker value
        print "JUMP/JUMPI: tgt address at the end: ";
        var r := SegBuilder.JUMPResolver(xs[0]);
        match r {
          case Left(address) => print "0x" + address;
          case Right(stackPos) => print "Peek(", stackPos, ")";
        }
        print "\n";
      }
      if xs[0].CONTSeg?  {
        if xs[0].lastIns.op.opcode != INVALID {
          var nextPC := xs[0].StartAddressNextSeg();
          print "CONT: PC of instruction after last is: " + " 0x" + NatToHex(nextPC) + "\n";
        }
        print "WeakestPre Operands:", k, "\n";
        print "WeakestPre Capacity:", l, "\n";
        print "Net Stack Effect:", xs[0].StackEffect(), "\n";
      } else {
        print "CONT: has an invaid instructiom" + "\n";
      }
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


  method PrintProofObjectToDafny(xs: seq<ProofObj>, pathToEVMDafny: string := "")
    requires forall i:: 0 <= i < |xs| ==> xs[i].IsValid()
  {
    if |pathToEVMDafny| > 0 {
      print "include \"", pathToEVMDafny, "/src/dafny/state.dfy\"", "\n";
      print "include \"", pathToEVMDafny, "/src/dafny/bytecode.dfy\"", "\n";
      print "\n";
    }

    print "module DafnyEVMProofObject {", "\n";

    print "import opened Int", "\n";
    print "import EvmState", "\n";
    print "import opened Bytecode", "\n";

    // Print validJumpDests lemma
    var j := CollectJumpDestAsString(CollectJumpDest(xs));
    if |j| > 0 {
      print "/** Lemma for Jumpdest */", "\n";
      print "lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)", "\n";
      print j;
      print "\n";
    }


    PrintProofObjectBody(xs);
    print "}", "\n";
  }

  /**
    *   Print out each linear segment as a Dafny function.
    *   Instructions are the Dafny-EVM instructions.
    */
  method {:tailrec} PrintProofObjectBody(xs: seq<ProofObj>, num: nat := 0)
    requires forall i:: 0 <= i < |xs| ==> xs[i].IsValid()
  {

    if |xs| > 0 {
      // 
      var startAddress := NatToHex(xs[0].s.Ins()[0].address);
      print "\n/** Code starting at 0x", startAddress,  " */\n";
      print "function {:opaque} ExecuteFromTag_", num, "(s0: EvmState.ExecutingState): (s': EvmState.State)\n";
      print "  requires s0.PC() == 0x", startAddress, " as nat\n";

      print "  // Net Operands effect " ;
      print xs[0].s.NetOpEffect() ;
      print "\n";
      print "  requires s0.Operands() >= ";
      print xs[0].wpOp ;
      print "\n";
      print "  // Net Capacity effect " ;
      print xs[0].s.NetCapEffect() ;
      print "\n";
      print "  requires s0.Capacity() >= ";
      print xs[0].wpCap;

      print "\n";
      //    If jump and target of jump is known print it.
      assert xs[0].s.IsValid();
      if xs[0].JUMP? && xs[0].s.lastIns.op.IsJump() {
        { match xs[0].tgt
          case Right(v) =>
            print "  requires s0.IsJumpDest(s0.Peek(", v, "))\n";
          case _ => print ""  ;
        }
      }

      match xs[0] {
        case JUMP(s, _, _, tgt, _) =>
          print "  ensures s'.EXECUTING?\n";
          print "  ensures s'.PC() ==  ";
          { match tgt
            case Left(xc) => print "0x", xc;
            case Right(v) =>
              print "s0.Peek(", v, ") as nat";
          }
          //  If JUMPI PC could be either tgt or instruction after last.
          if s.lastIns.op.opcode == JUMPI {
            print " || s'.PC() == 0x", NatToHex(s.lastIns.address + 1);
          }
          print "\n";
          //    Print the constraint for the net stack size effect
          var n := xs[0].StackEffect();
          print "  ensures s'.Operands() == s0.Operands()";
          if n >= 0 { print " + ", n; } else { print " - ", -n; }
          print "\n";

        case CONT(s, _, _, _) =>
          print "  ensures s'.EXECUTING?\n";
          //    PC at the end is the address right after last instruction.
          //   var nextPC := s.lastIns.address + 1 + |s.lastIns.arg|;
          //   assume |s.lastIns.arg| % 2 == 0;
          if s.lastIns.op.opcode != INVALID {
            var nextPC := s.StartAddressNextSeg();
            print "  ensures s'.PC() == 0x" + NatToHex(nextPC) + "\n";
            //    Print the constraint for the net stack size effect
            var n := xs[0].StackEffect();
            print "  ensures s'.Operands() == s0.Operands()";
            if n >= 0 { print " + ", n; } else { print " - ", -n; }
          } else {
            print "  Last instruction is invalid";
          }
          print "\n";

        case TERMINAL(s, _, _, _) =>
          print "  ensures s'.RETURNS?\n";
      }

      print "{\n";
      print "  ValidJumpDest(s0);\n";
      PrintInstructionsToDafny(xs[0].s.Ins());
      print "  s", |xs[0].s.Ins()|, "\n";
      print "}\n";
      PrintProofObjectBody(xs[1..], num + 1);
    }
  }

  /**
    *   Print out a sequence of instructions in the Dafny-EVM format.
    */
  method PrintInstructionsToDafny(xs:seq<ValidInstruction>, pos: nat := 0)
  {
    if |xs| > 0 {
      var k := PrintInstructionToDafny(xs[0], pos, pos + 1);
      print "  ", k, "\n";
      PrintInstructionsToDafny(xs[1..], pos + 1);
    }
  }
}

