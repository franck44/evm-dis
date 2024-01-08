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
include "../../../src/dafny/utils/EVMObject.dfy"
include "../../../src/dafny/utils/CFGState.dfy"
include "../../../src/dafny/utils/MiscTypes.dfy"

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
  import opened EVMObject
  import opened CFGState
  import opened MiscTypes


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
  method TestPost(post: ValidCond, s: ValidLinSeg, jumpDests: seq<nat> := [])
    requires post.StCond?
  {
    var pre := s.WPre(post);
    var s0 := BuildInitState(pre);
    for i := 0 to s.NumberOfExits() {
      var s1 := s.Run(s0, i, jumpDests);
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

  //  Simple example
  method {:test} Test1()
  {
    //  Push and JUMP
    var x := DisassembleU8([PUSH1, 0x0a, PUSH1, 0x08, PUSH1, 0x03, SWAP1, PUSH1, 0x13, JUMP] );
    expect |x| == 6;
    var y := SplitUpToTerminal(x);
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
    TestPost(c2, y[0], [0x13]);


    var c3 := StCond([3], [0x10]);
    var r3 := y[0].WPre(c3);
    expect r3 == StCond([0], [0x10]);
    TestPost(c3, y[0], [0x13]);
  }

  /** POP then DUP1 */
  method {:test} {:verify true} Test4()
  {
    //  Linear segment
    var x := DisassembleU8([POP, DUP1]);
    expect |x| == 2;
    var y := SplitUpToTerminal(x);
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

  method {:timeLimitMultiplier 1} {:test} Test5()
  {
    var x := DisassembleU8(
      [
        /* 0x00: */ PUSH1, 0x05,
        /* 0x02: */ PUSH1, 0x0d,
        /* 0x04: */ JUMP,

        /* 0x05: */ JUMPDEST,
        /* 0x06: */ PUSH1, 0x0b,
        /* 0x08: */ PUSH1, 0x0d,
        /* 0x0a: */ JUMP,

        /* 0x0b: */ JUMPDEST,
        /* 0x0c: */ STOP,

        /* 0x0d: */ JUMPDEST,
        /* 0x0e: */ JUMP
      ]
    );

    expect |x| == 11;
    var y := SplitUpToTerminal(x);
    assert forall i, i' :: 0 <= i < i' < |y| ==> y[i].StartAddress() < y[i'].StartAddress();
    expect |y| == 4;

    // 
    expect y[0].StartAddress() == 0x00;
    var p: ValidEVMObj := EVMObj(y);

    var pStates := [DEFAULT_GSTATE];

    var pExits: seq<nat>  := [];
    // Create a path 0 -> 3 -> 1 -> 3
    for i := 0 to 3
      invariant |pStates| >= 1
      invariant |pStates| == |pExits| + 1
      invariant forall s:: s in pStates ==> s.IsBounded(|p.xs|)
      invariant forall k:: 0 <= k < |pExits| ==> pExits[k] < |p.NextG(pStates[k])|
    {
      expect Last(pStates).IsBounded(|p.xs|);
      expect |p.NextG(Last(pStates))| == 1;
      pStates := pStates + [p.NextG(Last(pStates))[0]];
      pExits := pExits + [0];
    }
    expect forall s:: s in pStates ==> s.EGState? && s.IsBounded(|p.xs|);
    var index := p.FindFirstNodeWithSegIndex(3, Init(pStates));
    expect index == Some(1);

    var d := p.SafeLoopFound(3, Init(pStates), pExits);
    expect d == None();

    //  Simulation of safeLoopGFound on the same path
    var pathFromIndex := Init(pStates)[index.v..];
    assert pathFromIndex[0].EGState? && pathFromIndex[0].segNum == 3;
    var exitsFromIndex : seq<nat> := pExits[index.v..];
    //  Map to the segment numbers
    var segmentsOnPathFromIndex : seq<nat> := seq(|pathFromIndex|, i requires 0 <= i < |pathFromIndex| => pathFromIndex[i].segNum);

    expect Last(pExits) == 0;
    expect p.xs[Last(pStates).segNum].NumberOfExits() == 1;
    var tgtCond := p.xs[Last(Init(pStates)).segNum].LeadsTo(p.xs[3].StartAddress(), Last(pExits));

    expect tgtCond == StTrue();
    expect |segmentsOnPathFromIndex| == |exitsFromIndex|;
    expect forall k:: 0 <= k < |segmentsOnPathFromIndex| ==> segmentsOnPathFromIndex[k] < |p.xs|;
    expect forall i:: 0 <= i < |exitsFromIndex| ==> exitsFromIndex[i] < p.xs[segmentsOnPathFromIndex[i]].NumberOfExits();
    var w1 := WPreSeqSegs(segmentsOnPathFromIndex, exitsFromIndex, tgtCond, p.xs, p.xs[3].StartAddress());

    expect w1 == StCond([0], [5]);
    var r :=  p.PreservesCond(w1, exitsFromIndex, 0x0d);

    expect r == false;
  }

}



