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

include "../../../src/dafny/utils/MiscTypes.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/utils/EVMObject.dfy"
include "../../../src/dafny/utils/CFGState.dfy"
include "../../../src/dafny/utils/MinimiserGState.dfy"
include "../../../src/dafny/utils/Partition.dfy"

module {:disableNonlinearArithmetic} BuildCFGSimplifiedTests {

  import opened MiscTypes
  import opened Int
  import opened BinaryDecoder
  import opened EVMConstants
  import opened Splitter
  import opened EVMObject
  import opened CFGState
  import opened GStateMinimiser
  import opened PartitionMod

  //  Simple example
  method {:test} {:verify true} Test10()
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
      var y := SplitUpToTerminal(x);
      expect |y| == 5;
      expect y[1].StartAddress() == 0x0a;
      expect y[2].StartAddress() == 0x13;
      expect y[3].StartAddress() == 0x1c;
      expect y[0].StartAddress() == 0;

      assert |y| >= 1;
      var p := EVMObj(y);
      var a1, _ := p.BuildCFG();
      assert a1.IsValid();
      print "Size of a1: ", a1.SSize(), "\n";
      a1.ToDot(nodeToString := (s, _) requires s in a1.states => p.ToHTML(s),
               labelToString := (s, l, _) requires s in a1.states && 0 <= l => p.DotLabel(s, l));

      //    Minimisation
      expect a1.SSize() >= 1;
      var p1: ValidPartition := PartitionMod.MakeInit(a1.SSize());

      //  create an equivalence relation on nodes
      var e :=
        (x:nat, y:nat) requires 0 <= x < a1.SSize() && 0 <= y < a1.SSize()
        => if x == y then
            true
          else
            match (a1.states[x], a1.states[y])
            case (EGState(s1,_), EGState(s2, _)) => s1 == s2
            case (_, _) => false
        ;
      assert IsEquivRel(e, a1.SSize());

      var vp: GStateMinimiser.Pair := Pair(a1, p1);
      var a2 := vp.Minimise();
      a2.ToDot(nodeToString := (s, _) requires s in a1.states => p.ToHTML(s),
               labelToString := (s, l, _) requires s in a1.states && 0 <= l => p.DotLabel(s, l));

    }
  }

  // Simple tester
  method {:main} {:verify true} Main(args: seq<string>)
  {
    {
      //  Make sure a string is passed to the program.
      expect |args| >= 2;
      var x := Disassemble(args[1]);

      var y := SplitUpToTerminal(x);
      print "segments: ", |y|, "\n";
      if |y| >= 1 {
        var p: ValidEVMObj := EVMObj(y);

        var a1, _ := p.BuildCFG();
        assert a1.IsValid();
        print "Size of a1: ", a1.SSize(), "\n";
        a1.ToDot(nodeToString := (s, _) requires s in a1.states => p.ToHTML(s),
                 labelToString := (s, l, _) requires s in a1.states && 0 <= l => p.DotLabel(s, l));

        //  Minimisation
        expect a1.SSize() >= 1;
        var p1: ValidPartition := PartitionMod.MakeInit(a1.SSize());

        //  create an equivalence relation on nodes
        var e :=
          (x:nat, y:nat) requires 0 <= x < a1.SSize() && 0 <= y < a1.SSize()
          => if x == y then
              true
            else
              match (a1.states[x], a1.states[y])
              case (EGState(s1,_), EGState(s2, _)) => s1 == s2
              case (_, _) => false
          ;
        assert IsEquivRel(e, a1.SSize());
        var p2 := p1.ComputeFinest(e);
        assert a1.IsValid();
        assert p2.n == a1.SSize();
        var vp: GStateMinimiser.ValidPair := Pair(a1, p2);
        var a2 := vp.Minimise();
        a2.ToDot(nodeToString := (s, _) requires s in a1.states => p.ToHTML(s),
                 labelToString := (s, l, _) requires s in a1.states && 0 <= l => p.DotLabel(s, l));
      } else {
        print "No segments\n";
      }
    }
  }
}