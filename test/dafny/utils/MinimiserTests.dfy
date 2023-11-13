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

/**
  * Test correct computation of next State.
  * 
  */
module MinimiserTests {

  const a := false
  const b := true

  import opened Minimiser
  import opened Automata
  import opened PartitionMod

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
    var p1 := Partition(5, [{0, 1, 2, 3}, {4}]);
    var m: map<(nat, bool), nat> :=
      map[
        (0, false) := 1, (0, true) := 2,
        (1, false) := 1, (1, true) := 3,
        (2, false) := 1, (2, true) := 2,
        (3, false) := 1, (3, true) := 4,
        (4, false) := 2, (4, true) := 1
      ];
    assert p1.IsValid();
    var a1 := Auto(5, m);

    var vp0 : ValidPair := Pair(a1, p1);

    var a2 := Minimise(vp0);
    print "Minimise result:\n";
    expect a2.p.elem == [{0, 2}, {1}, {3}, {4}];
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
    var p1 := Partition(4, [{0, 3}, {1, 2}]);
    var m: map<(nat, bool), nat> :=
      map[
        (0, a) := 1, (0, b) := 0,
        (1, a) := 2, (1, b) := 1,
        (2, a) := 1, (2, b) := 2,
        (3, a) := 1, (3, b) := 2
      ];
    assert p1.IsValid();
    var a1 := Auto(4, m);
    var vp0 : ValidPair := Pair(a1, p1);
    var a2 := Minimise(vp0);
    print "Minimise result:\n";
    expect a2.p.elem == [{0}, {3}, {1, 2}];
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
    var p1 := Partition(5, [{0, 1, 3, 2, 4}]);
    var m: map<(nat, bool), nat> :=
      map[
        (0, a) := 1,
        (0, b) := 3,
        (1, b) := 2,
        (3, b) := 4
      ];
    assert p1.IsValid();
    var a1 := Auto(5, m);

    var vp0 : ValidPair := Pair(a1, p1);

    var  vp1 := vp0.SplitFrom();
    expect vp1.p.elem == [{0}, {1, 2, 3, 4}];

    var vp2 := vp1.SplitFrom();
    expect vp2.p.elem == [{0}, {1, 3} , {2, 4}];

    var a2 := Minimise(vp0);
    expect a2.p.elem == [{0}, {1, 3}, {2, 4}];
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
    var p1 := Partition(5, [{0, 1, 3, 2}, {4}]);
    var m: map<(nat, bool), nat> :=
      map[
        (0, a) := 1, (0, b) := 3,
        (1, a) := 2, (1, b) := 4,
        (2, a) := 1, (2, b) := 4,
        (3, a) := 2, (3, b) := 4,
        (4, a) := 4, (4, b) := 4
      ];
    assert p1.IsValid();
    var a1 := Auto(5, m);

    var vp0 : ValidPair := Pair(a1, p1);

    var  vp1 := vp0.SplitFrom();
    expect vp1.p.elem == [{0}, {1, 2, 3}, {4}];

    var vp2 := vp1.SplitFrom();
    expect vp2.p.elem == [{0}, {1, 2, 3}, {4}];

    var a2 := Minimise(vp0);
    expect a2.p.elem == [{0}, {1, 2, 3}, {4}];
  }

}

