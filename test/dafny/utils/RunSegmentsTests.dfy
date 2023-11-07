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
include "../../../src/dafny/utils/int.dfy"

/**
  * Test correct computation of next State.
  * 
  */
module RuNSegTests {

  import opened OpcodeDecoder
  import opened EVMConstants
  import Int
  import opened State
  import opened StackElement
  import opened BinaryDecoder
  import opened Splitter

  //  Simple example
  method {:test} Test1()
  {
    {
      //  Push and JUMP
      var x := DisassembleU8([PUSH1, 0x0a, PUSH1, 0x08, PUSH1, 0x03, SWAP1, PUSH1, 0x13, JUMP] );
      expect |x| == 6;
      var y := SplitUpToTerminal(x, [], []);
      expect |y| == 1;
      expect y[0].JUMPSeg?;
      //    Run Segment exit false. Should be Error
      var s0 := DEFAULT_VALIDSTATE;
      var s' := y[0].Run(s0, false);
      expect s'.Error?;

      var s1 := y[0].Run(s0, true);
      expect s1.EState?;
      expect s1 == EState(0x13,  [Value(0x08), Value(0x03), Value(0x0a)]);
    }
  }

  /** POP then DUP1 */
  method {:test} {:verify true} Test4()
  {
    //  Linear segment
    var x := DisassembleU8([POP, DUP1]);
    expect |x| == 2;
    var y := SplitUpToTerminal(x, [], []);
    expect |y| == 1;
    expect y[0].CONTSeg?;
    //    Run Segment exit false. Should be Error
    var s0 := DEFAULT_VALIDSTATE;
    var s' := y[0].Run(s0, true);
    expect s'.Error?;

    //  Not enough stakc element
    var s1 := y[0].Run(s0, false);
    expect s'.Error?;

    //  Good
    var s2 := y[0].Run(s0.(stack := [Random(), Random()]), false);
    expect s2.EState?;
    expect s2 == EState(0x02, [Random(), Random()]);

    var s3 := y[0].Run(s0.(stack := [Random(), Random()]), true);
    expect s3.Error?;
  }

  /**   Run more than one segment
    *   max-return.bin program
    */
  method {:test} {:verify true} Test5()
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
    expect y[0].JUMPSeg?;
    expect y[1].RETURNSeg?;
    expect y[2].JUMPISeg?;
    expect y[3].JUMPSeg?;
    expect y[4].JUMPSeg?;
    //    Run Segment 0, exit true (JUMP)
    var s0 := DEFAULT_VALIDSTATE;
    var s1 := y[0].Run(s0, true);
    expect s1.EState?;
    expect s1.pc == 0x13;

    //  y[2] starts at 0x13, and JUMPI
    expect s1.pc == y[2].StartAddress();
    var s2 := y[2].Run(s1, true);
    expect s2.EState?;
    expect s2.pc == 0x1f;
    expect s2.stack == [Value(0x3), Value(0xa), Value(0x8)];

    //  y[4] starts at 0x1f, and JUMP
    expect s2.pc == y[4].StartAddress();
    var s3 := y[4].Run(s2, true);
    expect s3.EState?;
    expect s3.pc == 0x1c;
    expect s3.stack == [Value(0x0), Value(0xa), Value(0x3)];

    //  y[3] starts at 0x1c, and JUMP
    expect s3.pc == y[3].StartAddress();
    var s4 := y[3].Run(s3, true);
    expect s4.EState?;
    expect s4.pc == 0xa;
    expect s4.stack == [Value(0x3)];

    //  y[1] starts at 0x0a, and RETURN
    expect s4.pc == y[1].StartAddress();
    var s5 := y[1].Run(s4, false);
    expect s5.EState?;
    //  We end up after RETURN.
    expect s5 == EState(0x12 + 1, [Value(64), Value(32), Random()]);

    //  Now test JUMPI false (we go directly to successor of JUMPI)
    //  y[2] starts at 0x13, and JUMPI
    expect s1.pc == y[2].StartAddress();
    var s2' := y[2].Run(s1, false);
    expect s2'.EState?;
    expect s2' == EState(0x1c,  [Value(0x3), Value(0xa), Value(0x8)]);

    //  y[3] starts at 0x1c, and JUMP
    expect s2'.pc == y[3].StartAddress();
    var s3' := y[3].Run(s2', true);
    expect s3'.EState?;
    expect s3' == EState(0x0a,  [Value(0x8)]);

    //  y[1] starts at 0x0a, and RETURN
    expect s3'.pc == y[1].StartAddress();
    var s4' := y[1].Run(s3', false);
    expect s4' == EState(0x12 + 1,  [Value(64), Value(32), Random()]);

  }
}

