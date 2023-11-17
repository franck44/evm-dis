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
include "../../../src/dafny/utils/CFGraph.dfy"
include "../../../src/dafny/CFGBuilder/BuildCFG.dfy"

/**
  * Test correct computation of Wpre on segments.
  * 
  */
module LoopTests {

  import opened OpcodeDecoder
  import opened EVMConstants
  import Int
  import opened State
  import opened StackElement
  import opened BinaryDecoder
  import opened Splitter
  import opened WeakPre
  import opened LinSegments
  import opened BuildCFGraph
  import opened CFGraph
  import opened MiscTypes

  //  Helpers
  function BuildInitState(c: ValidCond): (s: AState)
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
  method {:notest} Test0() {
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
  method {:notest} Test1()
  {
    //  Push and JUMP
    var x := DisassembleU8(
      [
        /* 00000000: */ PUSH0,
        /* 00000001: */ DUP1,

        /* 00000002: */ JUMPDEST,
        /* 00000003: */ PUSH1, 0x0a,
        /* 00000005: */ DUP2,
        /* 00000006: */ LT,
        /* 00000007: */ PUSH1, 0x13,
        /* 00000009: */ JUMPI,

        /* 0000000a: */ POP,
        /* 0000000b: */ PUSH1, 0x40,
        /* 0000000d: */ MSTORE,
        /* 0000000e: */ PUSH1, 0x20,
        /* 00000010: */ PUSH1, 0x40,
        /* 00000012: */ RETURN,

        /* 00000013: */ JUMPDEST,
        /* 00000014: */ SWAP1,
        /* 00000015: */ PUSH1, 0x01,
        /* 00000017: */ PUSH1, 0x0a,
        /* 00000019: */ SWAP2,
        /* 0000001a: */ ADD,
        /* 0000001b: */ SWAP2,
        /* 0000001c: */ SWAP1,
        /* 0000001d: */ POP,
        /* 0000001e: */ PUSH1, 0x02,
        /* 00000020: */ JUMP
      ] );
    expect |x| == 25;
    var y := SplitUpToTerminal(x, [], []);
    expect |y| == 4;
    expect y[0].CONTSeg?;
    expect y[1].JUMPISeg?;
    expect y[2].RETURNSeg?;
    expect y[3].JUMPSeg?;

    //  execute 0, 1, 3
    var s0 := DEFAULT_VALIDSTATE;
    var s1 := y[0].Run(s0, false);
    expect s1.EState?;

    expect s1.PC() == y[1].StartAddress();
    var s2 := y[1].Run(s1, true);
    expect s2.EState?;

    expect s2.PC() == y[3].StartAddress();
    var s3 := y[3].Run(s2, true);
    expect s3.EState?;
    expect s3.PC() == y[1].StartAddress();

    //  Compute Wpre for 0, 1, 3 to end up in PC ==  y[1].StartAddress()
    var c := y[3].LeadsTo(y[1].StartAddress() as Int.u256);
    // print c, "\n";
    var r1 := y[3].WPre(c);
    expect r1 == StTrue();
    // print r1, "\n";

  }

  /** Max max example */
  method {:test} Test2()
  {
    //  Push and JUMP
    var x := DisassembleU8(
      [
        //  JUMP/JUMPI: tgt address at the end: 0x1b
        /* 00000000: */  PUSH1, 0x12,
        /* 00000002: */  PUSH1, 0x08,
        /* 00000004: */  PUSH1, 0x0e,
        /* 00000006: */  PUSH1, 0x03,
        /* 00000008: */  PUSH1, 0x0a,
        /* 0000000a: */  SWAP3,
        /* 0000000b: */  PUSH1, 0x1b,
        /* 0000000d: */  JUMP,

        //  Segment 1
        // JUMP/JUMPI: tgt address at the end: 0x1b
        /* 0000000e: */  JUMPDEST,
        /* 0000000f: */  PUSH1, 0x1b,
        /* 00000011: */  JUMP,

        //  Segment 2
        /* 00000012: */  JUMPDEST,
        /* 00000013: */  PUSH1, 0x40,
        /* 00000015: */  MSTORE,
        /* 00000016: */  PUSH1, 0x20,
        /* 00000018: */  PUSH1, 0x40,
        /* 0000001a: */  RETURN,

        //  Segment 3
        // JUMP/JUMPI: tgt address at the end: 0x27
        /* 0000001b: */  JUMPDEST,
        /* 0000001c: */  SWAP2,
        /* 0000001d: */  SWAP1,
        /* 0000001e: */  DUP1,
        /* 0000001f: */  DUP4,
        /* 00000020: */  LT,
        /* 00000021: */  PUSH1, 0x27,
        /* 00000023: */  JUMPI,

        //  Segment 4
        // JUMP/JUMPI: tgt address at the end: Peek(1)
        /* 00000024: */  JUMPDEST,
        /* 00000025: */  POP,
        /* 00000026: */  JUMP,

        //  Segment 5
        // JUMP/JUMPI: tgt address at the end: 0x24
        /* 00000027: */  JUMPDEST,
        /* 00000028: */  SWAP1,
        /* 00000029: */  SWAP2,
        /* 0000002a: */  POP,
        /* 0000002b: */  SWAP1,
        /* 0000002c: */  PUSH0,
        /* 0000002d: */  PUSH1, 0x24,
        /* 0000002f: */  JUMP
      ] );

    var xs := [
      (0, true),
      (3, false),
      (4, true),
      (1, true)
        //   (1, true)
    ];

    // expect |x| == 25;
    var y := SplitUpToTerminal(x, [], []);
    expect |y| == 6;
    expect y[0].JUMPSeg?;
    expect y[1].JUMPSeg?;
    expect y[2].RETURNSeg?;
    expect y[3].JUMPISeg?;
    expect y[4].JUMPSeg?;
    expect y[5].JUMPSeg?;

    //    Run the path specified by xs
    //    Run Segment 0, exit true (JUMP)
    var s0 := DEFAULT_VALIDSTATE;
    var s := s0;
    assert s.pc == 0;
    var seen: seq<CFGNode> := [CFGNode([], Some(0))];
    var seenPCs: seq<nat> := [0];
    var path: seq<bool> := [];

    //    Stop minus blocks before the end
    print "\n";
    for k := 0 to |xs|
    {
      expect s.EState?;
      expect s.pc == y[xs[k].0].StartAddress();
      s := y[xs[k].0].Run(s, xs[k].1);

      expect s.EState?;
      path := path + [xs[k].1];
      var n := CFGNode(path, PCToSeg(y, s.pc));
      seen := seen + [n];
      seenPCs := seenPCs + [s.pc];
      print "segment ", xs[k], " leads to ", s.ToString(), "\n";
      print "path is: ", path, "\n";
      print "SeenPCs is: ", seenPCs, "\n";
      print "Seen is: ", seen, "\n";
    }

    //     collect segment of PC of last state
    expect s.EState?;
    var last := PCToSeg(y, s.pc);
    expect last.Some?;
    expect last.v == 3;

    print "---- Stepping in last segment: ", last.v, "----\n";
    expect |seenPCs| >= 1;
    print "seen last PC? ", s.pc in seenPCs[..|seenPCs| - 1], "\n";

    expect s.pc < Int.TWO_256;
    expect |seen| == |path| + 1;
    expect forall k:: k in seen ==> k.seg.Some? && k.seg.v < |y|;
    expect |seen| > 1;
    expect y[seen[|seen| - 2].seg.v].JUMPSeg? || y[seen[|seen| - 2].seg.v].JUMPISeg? ;
    print "current PC is: ", s.pc, "(0x",  (Hex.NatToHex(s.pc)), ")", "\n";
    print "path is: ", path, "\n";
    print "SeenPCs is: ", seenPCs[..|seenPCs| - 1], "\n";
    print "Seen is: ", seen, "\n";
    expect |seen| > 0;
    var safe := SafeLoopFound(y, s.pc, seen[..|seen| - 1], path[..|path| - 1] + [true]);
    expect safe.None?;
    print "Safe to loop back?", safe, "\n";
    // print "last segment is:", last.v, "\n";

    

  }

}



