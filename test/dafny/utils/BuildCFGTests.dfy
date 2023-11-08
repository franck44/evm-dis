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
include "../../../src/dafny/utils/LinSegments.dfy"
include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/CFGBuilder/BuildCFG.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/prettyprinters/Pretty.dfy"

/**
  * Test correct computation of next State.
  * 
  */
module BuildCFGTests {

  import opened OpcodeDecoder
  import opened EVMConstants
  import Int
  import opened State
  import opened StackElement
  import opened BinaryDecoder
  import opened Splitter
  import opened BuilCFGraph
  import opened PrettyPrinters

  //  Simple example
  method {:test1} Test1()
  {
    {
      //  Push and JUMP
      var x := DisassembleU8([PUSH1, 0x0a, PUSH1, 0x08, PUSH1, 0x03, SWAP1, PUSH1, 0x13, JUMP] );
      expect |x| == 6;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 1;

      var s0 := DEFAULT_VALIDSTATE;
      var r := BuildCFG(y, 2) ;
      PrintToDot(y, r);

      //   var r3 := BuildCFGV3(y, 10) ;
      //   print "version 3\n";
      //   PrintToDotV3(y, r3.0);
    }
  }

  /** POP then DUP1 */
  //   method {:test} {:verify true} Test4()
  //   {
  //     //  Linear segment
  //     var x := DisassembleU8([POP, DUP1]);
  //     expect |x| == 2;
  //     var y := SplitUpToTerminal(x, [], []);
  //     expect |y| == 1;
  //     expect y[0].CONTSeg?;
  //     //    Run Segment exit false. Should be Error
  //     var s0 := DEFAULT_VALIDSTATE;
  //     var s' := y[0].Run(s0, true);
  //     expect s'.Error?;

  //     //  Not enough stakc element
  //     var s1 := y[0].Run(s0, false);
  //     expect s'.Error?;

  //     //  Good
  //     var s2 := y[0].Run(s0.(stack := [Random(), Random()]), false);
  //     expect s2.EState?;
  //     expect s2 == EState(0x02, [Random(), Random()]);

  //     var s3 := y[0].Run(s0.(stack := [Random(), Random()]), true);
  //     expect s3.Error?;
  //   }

  /**   Run more than one segment
    *   max-return.bin program
    */
  method {:test1} {:verify true} Test5()
  {
    //  Linear segment
    var x := DisassembleU8(
      [
        /* 00000000: */ PUSH1, 0x0a,
        /* 00000002: */ PUSH1, 0x08,
        /* 00000004: */ PUSH1, 0x03,
        /* 00000006: */ SWAP1,
        /* 00000007: */ PUSH1, 0x13,
        /* 00000009: */ JUMP,

        /* 0000000a: */ JUMPDEST,
        /* 0000000b: */ PUSH1, 0x40,
        /* 0000000d: */ MSTORE,
        /* 0000000e: */ PUSH1, 0x20,
        /* 00000010: */ PUSH1, 0x40,
        /* 00000012: */ RETURN,

        /* 00000013: */ JUMPDEST,
        /* 00000014: */ SWAP2,
        /* 00000015: */ SWAP1,
        /* 00000016: */ DUP1,
        /* 00000017: */ DUP4,
        /* 00000018: */ LT,
        /* 00000019: */ PUSH1, 0x1f,
        /* 0000001b: */ JUMPI,

        /* 0000001c: */ JUMPDEST,
        /* 0000001d: */ POP,
        /* 0000001e: */ JUMP,

        /* 0000001f: */ JUMPDEST,
        /* 00000020: */ SWAP1,
        /* 00000021: */ SWAP2,
        /* 00000022: */ POP,
        /* 00000023: */ SWAP1,
        /* 00000024: */ PUSH0,
        /* 00000025: */ PUSH1, 0x1c,
        /* 00000027: */ JUMP
      ]
    );
    expect |x| == 31;
    var y := SplitUpToTerminal(x, [], []);
    expect |y| == 5;
    expect y[1].StartAddress() == 0x0a;
    expect y[2].StartAddress() == 0x13;
    expect y[3].StartAddress() == 0x1c;
    var r := BuildCFG(y, 10) ;

    print "version 1\n";
    PrintToDot(y, r);

    var r2 := BuildCFGV2(y, 10) ;
    print "version 2\n";

    PrintToDot(y, r2.0);

    var r3 := BuildCFGV3(y, 10) ;
    print "version 3\n";

    PrintToDotV3(y, r3.0, r3.1);
    // PrintSegments(y);
  }

  /** max-max. */
  method {:test} {:verify false} Test6()
  {
    var x := Disassemble("60126008600e6003600a92601b565b601b565b60405260206040f35b91908083106027575b50565b909150905f602456");
    // expect |x| == 31;
    var y := SplitUpToTerminal(x, [], []);
    // expect |y| == 5;
    // expect y[1].StartAddress() == 0x0a;
    // expect y[2].StartAddress() == 0x13;
    // expect y[3].StartAddress() == 0x1c;
    var r := BuildCFGV3(y, 10) ;
    PrintToDotV3(y, r.0, r.1);
    // print "version 1\n";
    // PrintToDot(y, r);

    // var r2 := BuildCFGV2(y, 10) ;
    // print "version 2\n";

    // PrintToDot(y, r2.0);
  }
}

