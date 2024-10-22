/*
 * Copyright 2024 Franck Cassez
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
  method {:test} {:verify true} Test00()
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
      invariant forall i:: 0 <= i < |path.exits| ==> path.exits[i] < |prog.NextG(path.states[i])|
    {
      expect s.EGState?;
      print "Executing segment ", s.segNum, " starting at (", Hex.NatToHex(prog.StartAddress(s.segNum)), ")", "\n";
      expect exits[k] < prog.xs[s.segNum].NumberOfExits();
      s := prog.NextG(s)[exits[k]];
      expect s.EGState?;
      var x := prog.FindFirstNodeWithSegIndex(s.segNum, path.states);
    //   assume forall i:: 0 <= i < |path.exits| ==> path.exits[i] < |prog.NextG(path.states[i])|;
      print "FindFirst node with index ", s.segNum, " is ", x, "\n";
      var loopFound := prog.SafeLoopFound(s.segNum, path.states, path.exits + [exits[k]]); 
      print "Safe to loop back? ", loopFound, "\n";

      path := Path(path.states + [s], path.exits + [exits[k]]);
      seenSegs := seenSegs + [s.segNum];
      print " leads to state ", s.ToString(), "\n";
      PrintPath(path);
      print "\n";
      
    } 

  }
}
