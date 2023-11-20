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


include "../../../src/dafny/utils/StackElement.dfy"
include "../../../src/dafny/utils/State.dfy"
include "../../../src/dafny/utils/Instructions.dfy"
include "../../../src/dafny/disassembler/OpcodeDecoder.dfy"
include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/LinSegments.dfy"
include "../../../src/dafny/prettyprinters/Pretty.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/CFGBuilder/BuildCFG.dfy"
/**
  * Test correct computation of next State.
  * 
  */ 
module NextStateTests { 

  import opened MiscTypes
  import opened OpcodeDecoder
  import opened EVMConstants
  import opened Instructions
  import Int
  import opened State
  import opened StackElement
  import opened BinaryDecoder
  import opened PrettyPrinters
  import opened Splitter
  import opened BuildCFGraph 
  import opened LinSegments

  /** Arithmetic instruction. Proofs. */


  /**   RJUMP (not implemented an result in Error). */
  method {:test} Test1()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(RJUMPI));
      expect i.NextState(s, true).Error?;
      expect i.NextState(s, false).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(RJUMPV));
      expect i.NextState(s, true).Error?;
      expect i.NextState(s, false).Error?;
    }
  }

  
  method {:verify false} {:notmain} Main3(args: seq<string>)
  {
    if |args| < 2 {
      print "Not enough arguments\n";
    } else {
      var x := Disassemble(args[1], []);
      var y := SplitUpToTerminal(x, [], []);
      expect |y| >= 110;
      var xs := [
        (0, false),
        (1, false),
        (2, false),
        (3, false),
        (4, false),
        (5, false),
        (6, false),
        (7, false),
        (8, false),
        (9, false),
        (10, false),
        (11, true),
        (54, true),
        (56, true),
        (88, true),
        (67, true),
        (89, false),
        (90, false),
        (91, true),
        (93, true),
        (95, true),
        (97, true),  //
        (99, false)  //
      ];

      //    Run the path specified by xs
      //    Run Segment 0, exit true (JUMP)
      var s0 := DEFAULT_VALIDSTATE;
      var s := s0;
      //    Stop minus blocks before the end
      for k := 0 to |xs| 
      {
        expect s.EState?;
        expect s.pc == y[xs[k].0].StartAddress();
        s := y[xs[k].0].Run(s, xs[k].1);
        print "segment ", xs[k], " leads to ", s.ToString(), "\n";
      }

      //     collect segment of PC of last state
      expect s.EState?;
      var last := PCToSeg(y, s.pc);
      expect last.Some?;
      expect s.pc == y[last.v].StartAddress();
      print "---- Stepping in last segment: ", last.v, "----\n"; 
      for k := 0 to |y[last.v].Ins()| - 1
      {
        expect s.EState?;
        s := y[last.v].Ins()[k].NextState(s);
        print y[last.v].Ins()[k].op.name, " ", s.ToString(), "\n";
      }
      expect s.EState?;
      s := y[last.v].lastIns.NextState(s, true);
    //   expect s.EState?;
    //   print "\n", xs[upto], "\n";
      print y[last.v].lastIns.op.name, " ", s.ToString(), "\n";

    }
  }

}