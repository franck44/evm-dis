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


include "../../../src/dafny/utils/Minimiser.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/MiscTypes.dfy"

module MinimiserNat refines Minimiser {
  type T = nat
  const DEFAULT_STATE := 0

}

module MinimiserOptNat refines Minimiser  {

  type T = Option<nat>
  const DEFAULT_STATE := Some(0)

}

/**
  * Test correct computation of minimiser.
  * 
  */
module MinimiserTests {

  const a := false
  const b := true

  import opened MinimiserNat
  import opened MinimiserOptNat
  import opened Automata
  import opened PartitionMod
  import opened Int
  import opened MiscTypes

  method {:test} Test1()
  {
    /*
    automaton is:
    0 -- a -> 1 , 0 -- b -> 2 
    1 -- a -> 1, 1 -- b -> 3  
    2 -- a -> 1, 2 -- b -> 2
    3 -- a -> 1, 3 -- b -> 4 
    4 -- a -> 1, 4 -- b -> 2 

    4 is final.
    Minimised is:
    {0, 2} - F, T -> {1, 3} -- T -> {4}
    */
    var p1: ValidPartition := Partition(5, [{0, 1, 2, 3}, {4}]);
    var a1: ValidAuto<nat> := Auto().AddEdges(0, [1, 2]);
    var a2: ValidAuto<nat> := a1.AddEdges(1, [1, 3]);
    var a3: ValidAuto<nat> := a2.AddEdges(2, [1, 2]);
    var a4: ValidAuto<nat> := a3.AddEdges(3, [1, 4]);
    var a5: ValidAuto<nat> := a4.AddEdges(4, [1, 2]);

    assert p1.n == 5;
    expect a5.SSize() == 5;
    var vp0 : MinimiserNat.ValidPair := MinimiserNat.MakeInit(a5, p1);

    var vp1 := vp0.ClassSplitter();
    // PrintPartition(vp1.clazz);
    expect vp1.clazz.elem == [{0, 1, 2}, {3}, {4}];
    var vp2 := vp1.ClassSplitter();
    // PrintPartition(vp2.clazz);
    expect vp2.clazz.elem == [{0, 2}, {1}, {3}, {4}];
  }

  method {:test} Test2()
  {
      /*
      automaton is:
      0 -- a -> 1 , 0 -- b -> 0
      1 -- a -> 2, 1 -- b -> 1
      2 -- a -> 1, 2 -- b -> 2
      3 -- a -> 1, 3 -- b -> 2

      1, and 2 final. 3 is not accessible.
      Minimised is:
      {0} -- b -> {0}
      {0} -- a -> {1,2}
      {1, 2} -- a, b -> {1, 2}
      */
    var p1: ValidPartition := Partition(4, [{0, 3}, {1, 2}]);

    var a1: ValidAuto<nat> := Auto().AddEdges(0, [1, 0]);
    var a2: ValidAuto<nat> := a1.AddEdges(1, [2, 1]);
    var a3: ValidAuto<nat> := a2.AddEdges(2, [1, 2]);
    var a4: ValidAuto<nat> := a3.AddEdges(3, [1, 2]);

    assert p1.n == 4;
    expect a4.SSize() == 4;
    var vp0 : MinimiserNat.ValidPair := MinimiserNat.MakeInit(a4, p1);

    var vp1 := vp0.ClassSplitter();
    expect vp1.clazz.elem == [{0}, {3}, {1, 2}];
  }

  method {:test} Test3()
  {
    /*
    automaton is:
    0 -- a -> 1 -- b -> 2
    |_ b -> 3 -- b -> 4
    Minimised is:
    {0} - a, b -> {1, 3} -- b -> {2, 4}
    */
    var p1: ValidPartition := PartitionMod.MakeInit(5);

    var a0: ValidAuto<nat> := Auto();
    var a1 := a0.AddStates(seq(5, i => i));
    var a2: ValidAuto<nat> := a1.AddEdges(0, [3, 1]);
    var a3: ValidAuto<nat> := a2.AddEdges(1, [2]);
    var a4: ValidAuto<nat> := a3.AddEdges(3, [4]);

    // assert p1.IsValid();
    assert p1.n == 5;
    expect a4.SSize() == 5;
    var vp0 : MinimiserNat.ValidPair := MinimiserNat.MakeInit(a4, p1);

    var  vp1 := vp0.ClassSplitter();
    expect vp1.clazz.elem == [{0}, {1, 3} , {2, 4}];

  }

  method {:test} Test4()
  {
    /*
    automaton is:
    0 -- a -> 1 -- b -> 2
    |_ b -> 3 -- b -> 4
    Minimised is:
    {0} - a, b -> {1, 3} -- b -> {2, 4}
    */
    var p1: ValidPartition :=  Partition(5, [{0, 1, 2, 3}, {4}]);

    var a0: ValidAuto<nat> := Auto();
    var a1 := a0.AddStates(seq(5, i => i));
    var a2: ValidAuto<nat> := a1.AddEdges(0, [1, 3]);
    var a3: ValidAuto<nat> := a2.AddEdges(1, [2, 4]);
    var a4: ValidAuto<nat> := a3.AddEdges(2, [1, 4]);
    var a5: ValidAuto<nat> := a4.AddEdges(3, [2, 4]);
    var a6: ValidAuto<nat> := a5.AddEdges(4, [4, 4]);

    assert p1.n == 5;
    expect a6.SSize() == 5;
    var vp0 : MinimiserNat.ValidPair := MinimiserNat.MakeInit(a6, p1);

    var  vp1 := vp0.ClassSplitter();
    expect vp1.clazz.elem == [{0}, {1, 2, 3}, {4}];
  }

  method {:test} Test5()
  {
    /*
    automaton is:
              |----a <---|
    0 -- a -> 1 -- b -> 2 
    |_ b -> 3 -- b -> 4 
            ^--- a ---|    
    Minimised is:
    {0} - a, b -> {1, 3} -- b -> {2, 4}
    */
    var p1: ValidPartition := Partition(6, [{0, 1, 3}, {2, 4}, {5}]);

    var a0: ValidAuto<Option<nat>> := Auto();
    var a1 := a0.AddStates(seq(5, i => Some(i)) + [None]);
    var a2: ValidAuto<Option<nat>> := a1.AddEdges(Some(0), [Some(1), Some(3)]);
    var a3: ValidAuto<Option<nat>> := a2.AddEdges(Some(1), [None, Some(2)]);
    var a4: ValidAuto<Option<nat>> := a3.AddEdges(Some(2), [Some(1), None]);
    var a5: ValidAuto<Option<nat>> := a4.AddEdges(Some(3), [None, Some(4)]);
    var a6: ValidAuto<Option<nat>> := a5.AddEdges(Some(4), [Some(3), None]);

    assert p1.n == 6;
    expect a6.SSize() == 6;
    var vp0 : MinimiserOptNat.ValidPair := MinimiserOptNat.MakeInit(a6, p1);

    var  vp1 := vp0.ClassSplitter();
    expect vp1.clazz.elem ==  [{0}, {1, 3}, {2, 4}, {5}];

  }

}

