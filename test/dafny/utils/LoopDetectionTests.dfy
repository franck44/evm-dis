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
include "../../../src/dafny/utils/CFGState.dfy"
include "../../../src/dafny/utils/Instructions.dfy"
include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/WeakPre.dfy"
include "../../../src/dafny/utils/LinSegments.dfy"
include "../../../src/dafny/utils/EVMObject.dfy"

/**
  * Test correct computation of Wpre on segments.
  * 
  */
module LoopTests {

  import opened OpcodeDecoder
  import opened EVMConstants
  import Int
  import opened State
  import opened CFGState
  import opened StackElement
  import opened BinaryDecoder
  import opened Splitter
  import opened WeakPre
  import opened LinSegments
  import opened MiscTypes
  import opened EVMObject

  //  Helpers
  //   function BuildInitState(c: ValidCond): (s: AState)
  //   {
  //     var s0 := DEFAULT_VALIDSTATE;
  //     if c.StCond? then
  //       s0.(stack := BuildStack(c.TrackedPos(), c.TrackedVals()))
  //     else
  //       s0
  //   }

  //   /** Build an init stack that satifies a cond. */
  //   function BuildStack(pos: seq<nat>, vals: seq<Int.u256>, r: seq<StackElem> := []): (s: seq<StackElem>)
  //     requires |pos| == |vals|
  //   {
  //     if |pos| == 0 then r
  //     else
  //     if pos[0] < |r| then
  //       BuildStack(pos[1..], vals[1..], r[pos[0] := Value(vals[0])])
  //     else
  //       //  we have to add a suffix of pos[0] - |r| elements
  //       var suf := seq(pos[0] - |r|, _ => Random());
  //       assert |r + suf + [Value(vals[0])]| == pos[0] + 1;
  //       BuildStack(pos[1..], vals[1..], r + suf + [Value(vals[0])])
  //   }

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
  //   method TestPost(post: ValidCond, s: ValidLinSeg, jumps: seq<nat>)
  //     requires post.StCond?
  //   {
  //     var pre := s.WPre(post);
  //     expect !pre.StFalse?;
  //     var s0 := BuildInitState(pre);
  //     if s.HasExit(false) {
  //       var s1 := s.Run(s0, false, jumps);
  //       expect s1.EState?;
  //       expect s1.Size() >= MaxSeqVal(post.TrackedPos());
  //       for k := 0 to post.Size() {
  //         assert k < post.Size();
  //         expect post.TrackedPosAt(k) < s1.Size();
  //         expect s1.Peek(post.TrackedPosAt(k)) ==
  //                Value(post.TrackedValAt(k));
  //       }
  //       if s.HasExit(true) {
  //         var s1 := s.Run(s0, true, jumps);
  //         expect s1.EState?;
  //         expect s1.Size() >= MaxSeqVal(post.TrackedPos());
  //         for k := 0 to post.Size() {
  //           assert k < post.Size();
  //           expect post.TrackedPosAt(k) < s1.Size();
  //           expect s1.Peek(post.TrackedPosAt(k)) ==
  //                  Value(post.TrackedValAt(k));
  //         }
  //       }
  //     }

  //   }

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
    var y := SplitUpToTerminal(x);
    expect |y| == 4;
    expect y[0].CONTSeg?;
    expect y[1].JUMPISeg?;
    expect y[2].RETURNSeg?;
    expect y[3].JUMPSeg?;

    var jd := EVMObj(y).jumpDests;
    expect jd == [0x02, 0x13];

    //  execute 0, 1, 3
    var s0 := DEFAULT_VALIDSTATE;
    var s1 := y[0].Run(s0, 0, jd);
    expect s1.EState?;

    expect s1.PC() == y[1].StartAddress();
    var s2 := y[1].Run(s1, 1, jd);
    expect s2.EState?;

    expect s2.PC() == y[3].StartAddress();
    var s3 := y[3].Run(s2, 0, jd);
    expect s3.EState?;
    expect s3.PC() == y[1].StartAddress();

    //  Compute Wpre for 0, 1, 3 to end up in PC ==  y[1].StartAddress()
    var c := y[3].LeadsTo(y[1].StartAddress(), 0);
    // print c, "\n";
    var r1 := y[3].WPre(c);
    expect r1 == StTrue();
    // print r1, "\n";

  }

   method {:print} PrintPath(p: Path<GState>)
      requires |p.states| == |p.exits| + 1
    {
      print p.states[0].ToString();
      for i := 0 to |p.exits|
      {
        print " -- ", p.exits[i], " --> ", p.states[i + 1].ToString();
      }
    }

  /** Double loop example */
  method {:test} {:verify false} Test00()
  {
    var x := DisassembleU8(
      [
        // Segment 0
        /* 00000000: */ PUSH1, 0x02,
        //  Segment 1
        /* 00000002: */ JUMPDEST,
        // /* 00000003  */ PUSH0,
        // /* 00000004  */ SWAP1,
        /* 00000005: */ DUP1,
        /* 00000006: */ JUMP

      ]);
    var y := SplitUpToTerminal(x);
    expect |y| == 2;
    expect y[0].CONTSeg?;
    expect y[1].JUMPSeg?;

    var prog := EVMObj(y);
    var jd := prog.jumpDests;
    expect jd == [0x02];

    var exits := [0, 0, 0];

    //    Run the path specified by xs
    var s0 := DEFAULT_GSTATE;
    var s := s0;
    assert s.segNum == 0;
    expect y[0].StartAddress() == 0;

    var seenSegs: seq<nat> := [0];
    var path:= Path([DEFAULT_GSTATE], []);

    //   Execute all segments in |exits|
    print "Executing ", exits, "\n";
    for k := 0 to |exits|
      invariant |path.states| == |path.exits| + 1
      invariant forall s:: s in path.states ==> s.EGState? && s.IsBounded(|prog.xs|)
      invariant s.EGState? ==> s.IsBounded(|prog.xs|)
      invariant forall k:: 0 <= k < |path.exits| ==> path.exits[k] < |prog.NextG(s)| 
    {
      expect s.EGState?;
      print "Executing segment ", s.segNum, " starting at (", Hex.NatToHex(prog.StartAddress(s.segNum)), ")", "\n";
      expect exits[k] < prog.xs[s.segNum].NumberOfExits();
      s := prog.NextG(s)[exits[k]];
      expect s.EGState?;
      var x := prog.FindFirstNodeWithSegIndex(s.segNum, path.states);
      print "FindFirst node with index ", s.segNum, " is ", x, "\n";
      var loopFound := prog.SafeLoopFound(s.segNum, path.states, path.exits + [exits[k]]); 
      print "Safe to loop back? ", loopFound, "\n";

      path := Path(path.states + [s], path.exits + [exits[k]]);
      seenSegs := seenSegs + [s.segNum];
      print " leads to state ", s.ToString(), "\n";
      PrintPath(path);
      print "\n";
      
      //   print "SeenPCs is: ", seenPCs, "\n";
      //   print "Seen is: ", seen, "\n";
    } 

    //  print "--- Checks ---", "\n";
    // expect s.EState?;
    // var last := PCToSeg(y, s.pc);
    // expect last.Some?;
    // assert s.pc == y[last.v].StartAddress();
    // print "last :", last.v;
    // expect last.v == 1;

    //  Has it been seen before?
    // print "Checking if ", s.pc, " is in ", seenPCs[..|seenPCs| - 1], " ", s.pc in seenPCs[..|seenPCs| - 1], "\n";
    // print "path is: ", path, "\n";
    // print "Seen Nodes is: ", seen, "\n";

    // expect forall k:: k in seen && k.seg.Some? ==> k.seg.v < |y|;
    // var index := FindFirstNodeWithPC(y, s.pc, seen);
    // expect index == Some((CFGNode([false], Some(1)), 1));
    // print "Finding First occurrence of pc on seen: ", index.v, "\n";
    // // var path := seenOnPath[v.1..];
    // // //  compute the list of segments defined by the nodes in path
    // expect  forall k:: k in seen[index.v.1..] ==> k.seg.Some?;
    // var segs := NodesToSeg(seen[index.v.1..|seen| - 1]);
    // expect |segs| >= 2;
    // print "Path to test is: ", path[index.v.1..], "\n";
    // print "Segs to test are: ", segs, "\n";
    // expect  forall k {:triggers segs[k..]}:: 0 <= k < |segs| ==> k < |y|;

    // var wp1 := WPreSeqSegs(segs, path[index.v.1..], StTrue(), y, s.pc);
    // // // expect wp1 == StFalse();
    // print "wp1 :", wp1, "\n";

    // expect wp1.StCond?;
    // var st1 := wp1.BuildStack();
    // print "st1: ", st1, "\n";
    // var s1 := BuildInitState(wp1);
    // print "s1 :", s1.ToString(), "\n";

    // //  Run segments 1 from s1
    // var s2 := y[1].Run(s1, true, jd);
    // print "s2 :", s2.ToString(), "\n";
    // expect s2.EState?;
    // var b := s2.Sat(StCond([0, 2], [0x02, 0x4]));
    // print "S2.Sat(wp1): ", b, "\n";

  }

  /** Double loop example */
  //   method {:test2} Test2()
  //   {
  //     var x := DisassembleU8(
  //       [
  //         // Segment 0
  //         /* 00000000: */ PUSH1, 0x01,
  //         /* 00000002: */ PUSH0,

  //         // Segment 1
  //         /* 00000003: */ JUMPDEST,
  //         /* 00000004: */ PUSH1, 0x0a,
  //         /* 00000006: */ DUP2,
  //         /* 00000007: */ LT,
  //         /* 00000008: */ PUSH1, 0x14,
  //         /* 0000000a: */ JUMPI,

  //         // Segment 2
  //         /* 0000000b: */ POP,
  //         /* 0000000c: */ PUSH1, 0x40,
  //         /* 0000000e: */ MSTORE,
  //         /* 0000000f: */ PUSH1, 0x20,
  //         /* 00000011: */ PUSH1, 0x40,
  //         /* 00000013: */ RETURN,

  //         // Segment 3
  //         /* 00000014: */ JUMPDEST,
  //         /* 00000015: */ SWAP1,
  //         /* 00000016: */ PUSH0,

  //         // Segment 4
  //         /* 00000017: */ JUMPDEST,
  //         /* 00000018: */ PUSH1, 0x0a,
  //         /* 0000001a: */ DUP2,
  //         /* 0000001b: */ LT,
  //         /* 0000001c: */ PUSH1, 0x2c,
  //         /* 0000001e: */ JUMPI,

  //         // Segment 5
  //         /* 0000001f: */ POP,
  //         /* 00000020: */ PUSH1, 0x01,
  //         /* 00000022: */ PUSH1, 0x0a,
  //         /* 00000024: */ SWAP2,
  //         /* 00000025: */ ADD,
  //         /* 00000026: */ SWAP2,
  //         /* 00000027: */ SWAP1,
  //         /* 00000028: */ POP,
  //         /* 00000029: */ PUSH1, 0x03,
  //         /* 0000002b: */ JUMP,

  //         // Segment 6
  //         /* 0000002c: */ JUMPDEST,
  //         /* 0000002d: */ SWAP1,
  //         /* 0000002e: */ PUSH1, 0x02,
  //         /* 00000030: */ MUL,
  //         /* 00000031: */ SWAP1,
  //         /* 00000032: */ PUSH1, 0x17,
  //         /* 00000034: */ JUMP
  //       ] );

  //     var xs := [false, true, false, false, true];

  //     // expect |x| == 25;
  //     var y := SplitUpToTerminal(x, [], []);
  //     expect |y| == 7;
  //     expect y[0].CONTSeg?;
  //     expect y[1].JUMPISeg?;
  //     expect y[2].RETURNSeg?;
  //     expect y[3].CONTSeg?;
  //     expect y[4].JUMPISeg?;
  //     expect y[5].JUMPSeg?;
  //     expect y[6].JUMPSeg?;

  //     //    Run the path specified by xs
  //     var s0 := DEFAULT_VALIDSTATE;
  //     var s := s0;
  //     assert s.pc == 0;
  //     expect y[0].StartAddress() == 0;

  //     var jd := EVMObj(y).jumpDests;
  //     expect jd == [0x03, 0x14, 0x17, 0x2c];

  //     //  the nodes seen so far
  //     var seen: seq<CFGNode> := [CFGNode([], Some(0))];
  //     //  the corresponding PCs seen so far
  //     var seenPCs: seq<nat> := [0];
  //     //  the path (true|false) taken so far
  //     var path: seq<bool> := [];

  //     //   Execute all segments in |xs|
  //     print "Executing ", xs, "\n";
  //     for k := 0 to |xs|
  //       invariant |seen| == |seenPCs| == |path| + 1
  //       invariant s.EState?
  //     {
  //       var seg := PCToSeg(y, s.pc);
  //       expect seg.Some?;
  //       print "Executing segment ", seg.v, " pc(", Hex.NatToHex(s.pc), ")", "\n";
  //       //   expect s.pc == y[xs[k].0].StartAddress();
  //       s := y[seg.v].Run(s, xs[k], jd);
  //       expect s.EState?;
  //       path := path + [xs[k]];
  //       seen := seen + [CFGNode(path, PCToSeg(y, s.pc))];
  //       seenPCs := seenPCs + [s.pc];

  //       print " leads to state", s.ToString(), "\n";
  //       print "path is: ", path, "\n";
  //       print "SeenPCs is: ", seenPCs, "\n";
  //       print "Seen is: ", seen, "\n";
  //     }

  //     //  Here we are at the target segment

  //     // the pc should be the startAddress of 3
  //     //     collect segment of PC of last state

  //     print "--- Checks ---", "\n";
  //     expect s.EState?;
  //     var last := PCToSeg(y, s.pc);
  //     expect last.Some?;
  //     assert s.pc == y[last.v].StartAddress();
  //     expect last.v == 1;

  //     //  Has it been seen before?
  //     print "Checking if ", s.pc, " is in ", seenPCs[..|seenPCs| - 1], " ", s.pc in seenPCs[..|seenPCs| - 1], "\n";
  //     print "path is: ", path, "\n";
  //     print "Seen Nodes is: ", seen, "\n";

  //     expect forall k:: k in seen && k.seg.Some? ==> k.seg.v < |y|;
  //     var index := FindFirstNodeWithPC(y, s.pc, seen);
  //     expect index == Some((CFGNode([false], Some(1)), 1));
  //     print "Finding First occurrence of pc on seen: ", index.v, "\n";
  //     // var path := seenOnPath[v.1..];
  //     //  compute the list of segments defined by the nodes in path
  //     expect  forall k:: k in seen[index.v.1..] ==> k.seg.Some?;
  //     var segs := NodesToSeg(seen[index.v.1..|seen| - 1]);
  //     expect |segs| > 2;
  //     print "Path to test is: ", path[index.v.1..], "\n";
  //     print "Segs to test are: ", segs, "\n";
  //     expect  forall k {:triggers segs[k..]}:: 0 <= k < |segs| ==> k < |y|;

  //     var wp1 := WPreSeqSegs(segs, path[index.v.1..], StTrue(), y, s.pc);
  //     // expect wp1 == StFalse();
  //     print "wp1 :", wp1, "\n";

  //     //  Compute WPRe for segment 4 with StTrue
  //     var t1 := y[4].WPre(StTrue());
  //     print "t1 is: ", t1, "\n";
  //     //    Compute Wpre for feasibility of the segment, i.e. to ensure that
  //     //    the segment leads to to the next one.
  //     var t2 := y[4].LeadsTo(0x1f, false);
  //     print "t2 is: ", t2, "\n";

  //     // print
  //     // var x := SafeLoopFound();
  //     // print "---- Stepping in last segment: ", last.v, "----\n";
  //     // expect |seenPCs| >= 1;
  //     // print "seen last PC (in seenPCs -1) ? ", s.pc in seenPCs[..|seenPCs| - 1], "\n";
  //     // expect s.pc < Int.TWO_256;
  //     // print "Seen Nodes is: ", seen, "\n";
  //     // expect |seen| == |path| + 1;
  //     // expect forall k:: k in seen ==> k.seg.Some? && k.seg.v < |y|;
  //     // expect |seen| > 1;
  //     // expect y[seen[|seen| - 2].seg.v].JUMPSeg? || y[seen[|seen| - 2].seg.v].JUMPISeg? ;
  //     // print "current PC is: ", s.pc, "(0x",  (Hex.NatToHex(s.pc)), ")", "\n";
  //     // print "path is: ", path, "\n";
  //     // assert forall k:: k in seen ==> k.seg.Some? && k.seg.v < |y|;
  //     // // print "SeenPCs is: ", seenPCs[..|seenPCs| - 1], "\n";
  //     // expect |seen| > 0;
  //     // var ns := NodesToSeg(seen[..|seen| - 1]);
  //     // assert forall i:: 0 <= i < |ns| ==> ns[i] == seen[i].seg.v < |y|;
  //     // assert forall i:: 0 <= i < |ns| ==> ns[i] < |y| ;
  //     // print "Nodes to Seg is:", ns , "\n";
  //     // var pcond := y[1].LeadsTo(s.pc);
  //     // print "Post Condition (leadsTo) for segment 1  is:", pcond, "\n";
  //     // expect pcond.StTrue?;
  //     // //  compute precondition before 3, 4
  //     // expect |ns| > 2;
  //     // var wp1 := WPreSeqSegs(ns[2..|ns| - 1], pcond, y, s.pc);
  //     // print "Wpre for ", pcond ," before seg ", ns[2..|ns| - 1], " is: ", wp1 , "\n";
  //     // // print"WpreSeg on path: ", path[..|path| - 1] + [true], " is:", wp, "\n";    // print "last segment is:", last.v, "\n";
  //     // // var safe := SafeLoopFound(y, s.pc, seen[..|seen| - 1], path[..|path| - 1] + [true]);
  //     // // expect safe.None?;
  //     // // print "Safe to loop back?", safe, "\n";
  //     // expect |y[1].Ins()| == 3;
  //     // var wp2 := WPreIns(y[1].ins, pcond);
  //     // print "wp2:", wp2,"\n";
  //     // var wp3 := WPreIns(y[1].Ins()[1..2], wp2);
  //     // print y[1].Ins()[1].ToString(), "\n";
  //     // print "wp3:", wp3,"\n";

  //     // print "--- Computation of Wpres for each section", "\n";
  //     // for k := 1 to |xs|
  //     // {
  //     //   print "Prefix is:", ns[|xs| - k..|ns|], "\n";
  //     //   var wp1 := WPreSeqSegs(ns[|xs| - k..|ns|], StTrue(), y, s.pc);
  //     //   print "Wpre(", ns[|xs| - k..|ns|], ") for pc: ", s.pc, "(0x", (Hex.NatToHex(s.pc)), ") is: ", wp1, "\n";
  //     // }


  //     // var x1 := y[1].Ins()[1].Wpre();




  //   }



}



