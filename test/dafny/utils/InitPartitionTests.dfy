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

include "../../../src/dafny/utils/CFGraph.dfy"
include "../../../src/dafny/utils/MiscTypes.dfy"
include "../../../src/dafny/utils/Partition.dfy"
include "../../../src/dafny/utils/SeqOfSets.dfy"

/**
  * Test correct computation of default partition.
  * 
  */
module BuildCFGTests {

  import opened CFGraph
  import opened MiscTypes
  import opened PartitionMod
  import opened SeqOfSets

  //  Simple example
  method {:test} {:verify true} Test1()
  {
    {
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
      assert AllNonEmpty([s]);
      assert DisjointAnyTwo([s]);
      assert 0 < |[s]| <= r.0 + 1;
      assert SetN([s], r.0 + 1);
      var p: ValidPartition := Partition(0 + r.0 + 1, [s]); 
      assert p.n == r.0 + 1;
      assert |r.3| + 1 <= r.0 + 2;
      assert |r.3| <= r.0 + 1;
      assert forall k:: 0 <= k < p.n ==> k in numToCFGNode.Keys; 
      var p1 := SegNumPartition(p, numToCFGNode, 0); 
    //   PrintPartition(p1);
    }
  }


}

