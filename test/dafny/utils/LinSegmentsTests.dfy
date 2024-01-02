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

include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/prettyprinters/Pretty.dfy"

/**
  * Test equialence between segments.
  * 
  */
module EquivSegTests {

  import opened OpcodeDecoder
  import opened EVMConstants
  import opened BinaryDecoder
  import opened Splitter
  import opened LinSegments
  import PrettyPrinters

  method {:test} Test1()
  {
    {
      var x := DisassembleU8(
        [
          SWAP1,
          PUSH1, 0x13,
          JUMP,
          SWAP1,
          PUSH1, 0x10,
          JUMP
        ]
      );
      expect |x| == 6;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 2;

      expect y[0].JUMPSeg?;
      expect y[1].JUMPSeg?;
      expect EquivSeg(y[0], y[1]);
    }
  }

  method {:test} Test2()
  {
    {
      var x := DisassembleU8(
        [
          SWAP1,
          PUSH1, 0x13,
          JUMP,
          SWAP2,
          PUSH1, 0x10,
          JUMP
        ]
      );
      expect |x| == 6;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 2;

      expect y[0].JUMPSeg?;
      expect y[1].JUMPSeg?;
      expect !EquivSeg(y[0], y[1]);
    }
  }

  method {:test} Test3()
  {
    {
      var x := DisassembleU8(
        [
          SWAP2,
          PUSH1, 0x13,
          JUMPI,
          SWAP2,
          PUSH1, 0x10,
          JUMPI
        ]
      );
      expect |x| == 6;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 2;

      expect y[0].JUMPISeg?;
      expect y[1].JUMPISeg?;
      expect EquivSeg(y[0], y[1]);
    }
  }

  method {:test} Test4a()
  {
    {
      var x := DisassembleU8(
        [
          JUMPDEST,
          SWAP2,
          PUSH1, 0x13,
          DUP1,
          ADD,
          JUMPDEST,
          SWAP2,
          PUSH1, 0x13,
          DUP1,
          ADD
        ]
      );
      expect |x| == 10;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 2;
      // print "number of segments :", |y|, "\n";
      //   PrettyPrinters.PrintSegments(y);
      expect y[0].CONTSeg?;
      expect y[1].CONTSeg?;
      expect EquivSeg(y[0], y[1]);
    }
  }

  method {:test} Test4b()
  {
    {
      var x := DisassembleU8(
        [
          JUMPDEST
        ]
      );
      expect |x| == 1;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 1;

    }
  }

   method {:test} Test4c()
  {
    {
      var x := DisassembleU8(
        [
          JUMPDEST, JUMPDEST
        ]
      );
      expect |x| == 2;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 2;

    }
  }

  method {:test} Test5()
  {
    {
      var x := DisassembleU8(
        [
          JUMPDEST,
          SWAP2,
          PUSH1, 0x13,
          DUP1,
          ADD,
          JUMPDEST,
          SWAP3,
          PUSH1, 0x13,
          DUP1,
          ADD
        ]
      );
      expect |x| == 10;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 2;

      expect y[0].CONTSeg?;
      expect y[1].CONTSeg?;
      expect !EquivSeg(y[0], y[1]);
    }
  }

  method {:test} Test6()
  {
    {
      var x := DisassembleU8(
        [
          JUMPDEST,
          SWAP3,
          PUSH1, 0x13,
          DUP1,
          RETURN,
          JUMPDEST,
          SWAP3,
          PUSH1, 0x13,
          DUP1,
          RETURN
        ]
      );
      expect |x| == 10;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 2;

      expect y[0].RETURNSeg?;
      expect y[1].RETURNSeg?;
      expect EquivSeg(y[0], y[1]);
    }
  }

  method {:test} Test7()
  {
    {
      var x := DisassembleU8(
        [
          JUMPDEST,
          SWAP3,
          PUSH1, 0x13,
          DUP1,
          RETURN,
          JUMPDEST,
          SWAP3,
          PUSH1, 0x13,
          DUP1,
          STOP
        ]
      );
      expect |x| == 10;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 2;

      expect y[0].RETURNSeg?;
      expect y[1].STOPSeg?;
      expect !EquivSeg(y[0], y[1]);
    }
  }

}

