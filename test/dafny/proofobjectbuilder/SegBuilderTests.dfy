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

  method {:test} Test1()
  {
    //  Linear segment 
    var x := DisassembleU8([PUSH1, 0x0a, PUSH1, 0x08, PUSH1, 0x03, SWAP1, PUSH1, 0x13, JUMP] );
    var u := JUMPResolver(BuildSeg(x[..|x| - 1], x[|x| - 1]));
    expect u == Left(['1', '3']);
  }

  method {:test} Test2()
  {
    //  Linear segment 
    var x := DisassembleU8([JUMPDEST, POP, JUMP]);
    var u := JUMPResolver(BuildSeg(x[..|x| - 1], x[|x| - 1]));
    expect u == Right(1);
  }

  method {:test} Test3()
  {
    //  Linear segment 
    var x := DisassembleU8([JUMPDEST, SWAP2, SWAP1, DUP1, DUP4, LT, PUSH1, 0x1f, JUMPI]);
    var u := JUMPResolver(BuildSeg(x[..|x| - 1], x[|x| - 1]));
    expect u == Left(['1', 'f']);
  }

}

