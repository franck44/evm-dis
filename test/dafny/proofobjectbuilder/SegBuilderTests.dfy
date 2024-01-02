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

include "../../../src/dafny/utils/MiscTypes.dfy"
include "../../../src/dafny/utils/StackElement.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/proofobjectbuilder/SegmentBuilder.dfy"
include "../../../src/dafny/disassembler/Disassembler.dfy"

/**
  * Test computation of target JUMP/JUMPI.
  * 
  */
module SegBuilderTests {

  import opened MiscTypes
  import opened EVMConstants
  import opened Splitter
  import opened SegBuilder
  import opened BinaryDecoder
  import opened StackElement

  method {:test} {:verify true} Test1()
  {
    //  Linear segment
    var x := DisassembleU8([PUSH1, 0x0a, PUSH1, 0x08, PUSH1, 0x03, SWAP1, PUSH1, 0x13, JUMP]);
    expect |x| == 6;
    expect forall i:: 1 <= i < |x| ==> x[i].op.opcode != JUMPDEST;
    var seg := BuildSeg(x[..|x| - 1], x[|x| - 1]);
    expect seg.JUMPSeg?;
    var u := JUMPResolver(seg);
    expect u == Left(Value(0x13));
  }

  method {:test} {:verify true} Test2()
  {
    //  Linear segment
    var x := DisassembleU8([JUMPDEST, POP, JUMP]);
    expect |x| == 3;
    expect forall i:: 1 <= i < |x| ==> x[i].op.opcode != JUMPDEST;
    var seg := BuildSeg(x[..|x| - 1], x[|x| - 1]);
    expect seg.JUMPSeg?;
    var u := JUMPResolver(seg);
    expect u == Right(1);
  }

  method {:test} {:verify true} Test3()
  {
    //  Linear segment
    var x := DisassembleU8([JUMPDEST, SWAP2, SWAP1, DUP1, DUP4, LT, PUSH1, 0x1f, JUMPI]);
    expect |x| == 8;
    expect forall i:: 1 <= i < |x| ==> x[i].op.opcode != JUMPDEST;
    var seg := BuildSeg(x[..|x| - 1], x[|x| - 1]);
    expect seg.JUMPISeg?;
    var u := JUMPResolver(seg);
    expect u == Left(Value(0x1f));
  }

  method {:test} {:verify true} Test4()
  {
    //  Linear segment
    var x := DisassembleU8([POP, DUP1]);
    expect |x| == 2;
    expect forall i:: 1 <= i < |x| ==> x[i].op.opcode != JUMPDEST;
    var seg := BuildSeg(x[..|x| - 1], x[|x| - 1]);
    expect seg.CONTSeg?;
    expect |seg.lastIns.arg| % 2 == 0;
    expect seg.StartAddressNextSeg() == 0x02;
  }

}

