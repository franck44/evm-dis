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
include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/WeakPre.dfy"

/**
  * Test correct computation of Wpre on segments.
  * 
  */
module SegWpreTests {

  import opened OpcodeDecoder
  import opened EVMConstants
  import Int
  import opened State
  import opened StackElement
  import opened BinaryDecoder
  import opened Splitter
  import opened WeakPre
  import opened LinSegments

  //  Helpers
  function BuildInitState(c: ValidCond): (s: AState)
    // requires c.StCond?
  {
    var s0 := DEFAULT_VALIDSTATE;
    if c.StCond? then
      s0.(stack := BuildStack(c.TrackedPos(), c.TrackedVals()))
    else
      s0
  }

  /** Build an init stack that satifies a cond. */
  function BuildStack(pos: seq<nat>, vals: seq<Int.u256>, r: seq<StackElem> := []): (s: seq<StackElem>)
    requires |pos| == |vals|
  {
    if |pos| == 0 then r
    else
    if pos[0] < |r| then
      BuildStack(pos[1..], vals[1..], r[pos[0] := Value(vals[0])])
    else
      //  we have to add a suffix of pos[0] - |r| elements
      var suf := seq(pos[0] - |r|, _ => Random());
      assert |r + suf + [Value(vals[0])]| == pos[0] + 1;
      BuildStack(pos[1..], vals[1..], r + suf + [Value(vals[0])])
  }

  /** Tests the build stack function first. */
  method {:test} test0() {
    var c1 := StCond([2], [0x10]);
    var st1 := BuildInitState(c1);
    expect st1.stack == [Random(""), Random(""), Value(16)];

    var c2 := StCond([2, 0], [0x10, 0x20]);
    var st2 := BuildInitState(c2);
    expect st2.stack == [Value(0x20), Random(""), Value(16)];

    var c3 := StCond([2, 0, 5], [0x10, 0x20, 0x50]);
    var st3 := BuildInitState(c3);
    expect st3.stack == [Value(0x20), Random(""), Value(16), Random(), Random(), Value(0x50)];
  }

  function CheckStack(s: ValidState, post: ValidCond): bool
  {
    true
  }

  function MaxSeqVal(xs: seq<nat>, m: nat := 0): nat
  {
    if |xs| == 0 then m
    else if xs[0] > m then MaxSeqVal(xs[1..], xs[0])
    else  MaxSeqVal(xs[1..], m)
  }
 
  /**
    *   Sanity check.
    *   After computing the WPre of c, test that the post of
    *   the Wpre of c satisfies c.
    */
  method TestPost(post: ValidCond, s: ValidLinSeg)
    requires post.StCond?
  {
    var pre := s.WPre(post);
    var s0 := BuildInitState(pre);
    if s.HasExit(false) {
      var s1 := s.Run(s0, false);
      expect s1.EState?;
      expect s1.Size() >= MaxSeqVal(post.TrackedPos());
      for k := 0 to post.Size() {
        assert k < post.Size();
        expect post.TrackedPosAt(k) < s1.Size();
        expect s1.Peek(post.TrackedPosAt(k)) ==
               Value(post.TrackedValAt(k));
      }
      if s.HasExit(true) {
        var s1 := s.Run(s0, true);
        expect s1.EState?;
        expect s1.Size() >= MaxSeqVal(post.TrackedPos());
        for k := 0 to post.Size() {
          assert k < post.Size();
          expect post.TrackedPosAt(k) < s1.Size();
          expect s1.Peek(post.TrackedPosAt(k)) ==
                 Value(post.TrackedValAt(k));
        }
      }
    }

  }

  //  Simple example
  method {:test} Test1()
  {
    //  Push and JUMP
    var x := DisassembleU8([PUSH1, 0x0a, PUSH1, 0x08, PUSH1, 0x03, SWAP1, PUSH1, 0x13, JUMP] );
    expect |x| == 6;
    var y := SplitUpToTerminal(x, [], []);
    expect |y| == 1;
    expect y[0].JUMPSeg?;

    //    Compute various preconditions for this segment
    for k := 0 to 3 { //   interval 0..2
      var c1 := StCond([k], [0x10]);
      var r1 := y[0].WPre(c1);
      expect r1.StFalse?;
    }

    var c2 := StCond([4], [0x10]);
    var r2 := y[0].WPre(c2);
    expect r2 == StCond([1], [0x10]);
    TestPost(c2, y[0]);

    var c3 := StCond([3], [0x10]);
    var r3 := y[0].WPre(c3);
    expect r3 == StCond([0], [0x10]);
    TestPost(c3, y[0]);
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

    for k := 1 to 7 { //   interval 0..0
      var c1 := StCond([k], [0x10]);
      var r1 := y[0].WPre(c1);
      expect r1.StCond?;
      expect r1 == StCond([k], [0x10]);
    }

    { //   interval 0..0
      var c1 := StCond([0], [0x10]);
      var r1 := y[0].WPre(c1);
      expect r1.StCond?;
      expect r1 == StCond([1], [0x10]);
    }
  }
}



