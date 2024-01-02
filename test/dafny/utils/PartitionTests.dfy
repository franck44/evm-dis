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

include "../../../src/dafny/utils/Partition.dfy"

/**
  * Test correct computation of partitions.
  * 
  */
module PartitionTests {

  import opened PartitionMod

  method {:test} {:verify true} Test1()
  {
    {
      print "Killing test 1\n";
      var p := MakeInit(10);
      var f: (nat, nat) -> bool :=
        (x: nat, y: nat) => if x == y then true else x % 2 == y % 2;
      assert IsEquivRel(f, 10);
      var r := p.ComputeFinest(f);
      expect r.elem == [{0, 2, 4, 6, 8}, {1, 3, 5, 7, 9}];
    }
  }

  method {:test} {:verify true} Test2()
  {
    {
      print "Killing test 2\n";
      var p := MakeInit(10);
      var f: (nat, nat) -> bool :=
        (x: nat, y: nat) => if x == y then true else x / 2 == y / 2;
      assert IsEquivRel(f, 10);
      var r := p.ComputeFinest(f);
      expect r.elem == [{0, 1}, {2, 3}, {4, 5}, {6, 7}, {8, 9}];
    }
  }

  method {:test} {:verify false} Test3()
  {
    {
      print "Killing test 3\n";
      var p := MakeInit(10);
      var f: (nat, nat) -> bool :=
        (x: nat, y: nat) => if x == y then true else x % 2 == y % 2;
      assert IsEquivRel(f, 10);
      var r := p.ComputeFinest(f);
      expect r.elem == [{0, 2, 4, 6, 8}, {1, 3, 5, 7, 9}];
      var f1: (nat, nat) -> bool :=
        (x: nat, y: nat) => if x == y then true else x % 3 == y % 3;
      assert IsEquivRel(f1, 10);
      var r2 := r.RefineAll(f1);
      expect r2.elem == [{0, 6}, {2, 8}, {4}, {1, 7}, {3, 9}, {5}];
    }
  }



}

