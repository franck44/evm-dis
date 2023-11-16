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


// include "../../../src/dafny/utils/StackElement.dfy"
// include "../../../src/dafny/utils/State.dfy"
// include "../../../src/dafny/utils/LinSegments.dfy"
// include "../../../src/dafny/disassembler/disassembler.dfy"
// include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
// include "../../../src/dafny/CFGBuilder/BuildCFG.dfy"
include "../../../src/dafny/utils/CFGraph.dfy"
include "../../../src/dafny/utils/MiscTypes.dfy"
include "../../../src/dafny/utils/Partition.dfy"
  // include "../../../src/dafny/prettyprinters/Pretty.dfy"

/**
  * Test correct computation of next State.
  * 
  */
module BuildCFGTests {

  //   import opened OpcodeDecoder
  //   import opened EVMConstants
  //   import Int
  //   import opened State
  //   import opened StackElement
  //   import opened BinaryDecoder
  //   import opened Splitter
  //   import opened BuildCFGraph
  //   import opened PrettyPrinters
  import opened CFGraph
  import opened MiscTypes
  import opened PartitionMod

  //  Simple example
  method {:test} {:verify true} Test1()
  {
    {
      //  Push and JUMP
      //   var x := DisassembleU8([PUSH1, 0x0a, PUSH1, 0x08, PUSH1, 0x03, SWAP1, PUSH1, 0x13, JUMP] );
      //   expect |x| == 6;
      //   var y := SplitUpToTerminal(x, [], []);
      //   expect |y| == 1;
      //   expect y[0].StartAddress() == 0;
      //   var g := BuildCFGV4(y, 2);
      //   expect g.IsValid();
      //   var g' := g.Minimise();
      //   expect g'.IsValid();
      //   print "CFG Test1\n";
      //   assert g'.maxSegNum < |y|;
      //   print g'.DOTPrint(y);
      var s0 := CFGNode([], Some(0));
      var s1 := CFGNode([true]);
      var s2 := CFGNode([false]);
      var e := [
        BoolEdge(s0, true, s1),
        BoolEdge(s0, false, s2)
      ];
      var cfg1 := BoolCFGraph(e, 0); 
      var r := EdgesToMap(e, segUpperBound := 0);
      print "size of map: ", |r.3|;
      print " map:", r.3, "\n";
      var numToCFGNode := r.3;
      assert r.0 + 1 >= |r.3|;
      assert forall n:: 0 <= n <= r.0 ==> n in r.3.Keys;
      assert forall k:: k in numToCFGNode ==> k <= r.0;
      var s := set q {:nowarn} | 0 <= q <= r.0;
      assert {0} <= s;
      var p: ValidPartition := Partition(0 + r.0 + 1, [s]); 
      assert p.n == r.0 + 1;
      assert |r.3| + 1 <= r.0 + 2;
    //   calc <= {
    //     |r.3| + 1;
    //     r.0 + 2;
    //     |r.3| <= r.0 + 1; 
    //   }
      assert |r.3| <= r.0 + 1;
    //   assert forall n:: 0 <= n <= ==> n in numToCFGNode.Keys;
    //   assume 
      assert forall k:: 0 <= k < p.n ==> k in numToCFGNode.Keys; 
      var p1 := SegNumPartition(p, numToCFGNode, 0); 
    //   var cfg1 := BoolCFGraph();
      PrintPartition(p1);
    }
  }


}

