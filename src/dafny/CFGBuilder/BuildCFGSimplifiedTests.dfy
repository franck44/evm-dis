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
include "../utils/AutomataV2.dfy"

module BuildCFGSimplifiedTests { 

  import opened MiscTypes
  import opened DFSSimple
  import opened Int
  import opened AutomataV2

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
    // var g1: Graph<nat> := Graph(0 as nat, succ1);
    var a1, h1 := DFS(succ1, 0 as nat, History(0, [0]), Auto(x => NatToString(x)), 15);

    // expect a1 == Auto(map[0 := [1, 2], 1 := [3], 2 := [0, 1], 3 := [0]], 0);
    // expect a1.IsValid();
    print a1, " ", a1.SSize(), "\n";
    a1.ToDot();
  }

  method {:test} Test2() {
    // var g1: Graph<nat> := Graph(0 as nat, SimpleSucc);
    var a1, h1 := DFS(SimpleSucc, 0 as nat, History(0, [0]), Auto(x => NatToString(x)), 15);
    // expect a1 == Auto(map[0 := [1, 3], 1 := [2, 4], 2 := [3, 5], 3 := [1], 4 := [2], 5 := [3]], 0);
    // expect a1.IsValid();
    print a1, " ", a1.SSize(), "\n";
    a1.ToDot();
  }

  function f(n: nat, xs: seq<nat>): Option<nat>
  {
    if n in xs then Some(xs[0])
    else None
  }

  //   method Test<K(!new)>(f2: ValidFoo<K>) {
  //     var f1 : ValidFoo<nat> := f;
  //     var s := f1(1, [1, 2, 3]);
  //     assert s.Some? ==> s.v in [1, 2, 3];

  //     assert forall x: nat, xs: seq<nat> :: f1(x, xs).Some? ==> f(x, xs).v in xs;

  //     assert forall x: K, xs: seq<K> :: f2(x, xs).Some? ==> f2(x, xs).v in xs;

  //   }
}