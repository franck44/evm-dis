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

include "../utils/MiscTypes.dfy" 
include "../utils/int.dfy"
include "./BuildCFGSimplified.dfy"
include "../utils/Automata.dfy"
include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/utils/EVMObject.dfy"
include "../utils/State.dfy"
include "../utils/MinimiserAState.dfy"
include "../utils/Partition.dfy "
include "../utils/SeqOfSets.dfy"


module BuildCFGSimplifiedTests {

  import opened MiscTypes
  import opened DFSSimple
  import opened Int
  import opened Automata
  import opened BinaryDecoder
  import opened EVMConstants
  import opened Splitter
  import opened EVMObject
  import opened State
  import opened AStateMinimiser
  import opened PartitionMod
  import opened SeqOfSets

  function SimpleSucc(n: nat): seq<nat> { 
    if n <= 2 then [n + 1, n + 3]
    else [n - 2]
  }

  function succ1(n: nat): seq<nat> {
    if n == 0 then [1, 2]
    else if n == 1 then [3]
    else if n == 2 then [0, 1]
    else if n == 3 then [0]
    else []
  }

  method {:test} Test1() {
    var a: Auto<nat> := Auto();
    var a1, h1 := DFS(succ1, 0 as nat, History(0, [0]), a, 15);
    expect a1.transitionsNat ==map[0 := [1, 3], 1 := [2], 2 := [0], 3 := [0, 1]];
    expect a1.states == [0, 1, 3, 2];
    assert a1.IsValid();
    // print "a1 size: ", a1.SSize(), "\n";
    // a1.ToDot(x => NatToString(x));
  }

  method {:test} Test2() {
    var a: Auto<nat> := Auto();
    var a1, h1 := DFS(SimpleSucc, 0 as nat, History(0, [0]), a, 15);
    expect a1.states == [0, 1, 2, 3, 5, 4];
    expect a1.transitionsNat == map[0 := [1, 3], 1 := [2, 5], 2 := [3, 4], 3 := [1], 4 := [3], 5 := [2]];
    assert a1.IsValid();
    // print "a1 size ", a1.SSize(), "\n";
    // a1.ToDot(x => NatToString(x));
  }

  function f(n: nat, xs: seq<nat>): Option<nat>
  {
    if n in xs then Some(xs[0])
    else None
  }

  //  Simple example
  method {:test} Test10()
  {
    {
      //  Push and JUMP
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
      expect y[0].StartAddress() == 0;

      var p := EVMObj(y);
      var succ : AState -> seq<AState> := p.Next;
      var a1, h1 := DFS(
        succ,
        DEFAULT_VALIDSTATE,
        History(DEFAULT_VALIDSTATE, [DEFAULT_VALIDSTATE]),
        Auto(),
        15);
      assert a1.IsValid();
    //   print "Size of a1: ", a1.SSize(), "\n";
    //   a1.ToDot((x: AState) => p.ToHTML(x));

      //  Minimisation
      expect a1.SSize() >= 1;
      var p1: ValidPartition := PartitionMod.MakeInit(a1.SSize());

      //  create an equivalence relation on nodes
      var e :=
        (x:nat, y:nat) requires 0 <= x < a1.SSize() && 0 <= y < a1.SSize()
        => if x == y then true else match (a1.states[x], a1.states[y])
                                    case (EState(pc1,_), EState(pc2, _)) => p.PCToSeg(pc1).Some? && p.PCToSeg(pc2).Some? && p.PCToSeg(pc2) == p.PCToSeg(pc2)
                                    case (_, _) => false
        ;
      assert IsEquivRel(e, a1.SSize());

      var vp: AStateMinimiser.Pair := Pair(a1, p1);
      var a2 := vp.Minimise();
    //   a2.ToDot((x: AState) => p.ToHTML(x));

    }
  }

  // Simple example
  method {:main} Nested(args: seq<string>)
  {
    {
      //  Push and JUMP
      expect |args| >= 2;
      var x := Disassemble(args[1]);

      var y := SplitUpToTerminal(x, [], []);
      print "segments: ", |y|, "\n";

      var p := EVMObj(y);
      var succ : AState -> seq<AState> := p.Next;
      var a1, h1 := DFS(
        succ,
        DEFAULT_VALIDSTATE,
        History(DEFAULT_VALIDSTATE, [DEFAULT_VALIDSTATE]),
        Auto(),
        15);
      assert a1.IsValid();
      print "Size of a1: ", a1.SSize(), "\n";
      a1.ToDot((x: AState) => p.ToHTML(x));

      //  Minimisation
      expect a1.SSize() >= 1;
      var p1: ValidPartition := PartitionMod.MakeInit(a1.SSize());

      //  create an equivalence relation on nodes
      var e :=
        (x:nat, y:nat) requires 0 <= x < a1.SSize() && 0 <= y < a1.SSize()
        => if x == y then true else match (a1.states[x], a1.states[y])
                                    case (EState(pc1,_), EState(pc2, _)) => p.PCToSeg(pc1).Some? && p.PCToSeg(pc2).Some? && pc1 == pc2
                                    case (_, _) => false
        ;
      assert IsEquivRel(e, a1.SSize());
      var p2 := p1.ComputeFinest(e);

      var vp: AStateMinimiser.Pair := Pair(a1, p2);
      var a2 := vp.Minimise();
      a2.ToDot((x: AState) => p.ToHTML(x)); 
    }
  }
}