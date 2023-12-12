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

module DFSSimple {

  import opened MiscTypes
  import opened Int

  function FunctionByMethodTailRecursion(x: int, y: int := 0): (r: int) {
    x + y
  } by method {
    if x < 8 || x == 77 {
      return x + y;
    } else {
      r := FunctionByMethodTailRecursion(x - 1, y + 1);
    }
  }

  datatype Graph<!T(==)> = Graph(init: T, succ: T -> seq<T>)

  datatype Auto<!T(!new,==)> = Auto(toString: T -> string, transitions: map<T, seq<T>> := map[], states: seq<T> := [])
  {
    function addEdge(i: T, j: T): (a: Auto<T>)
      requires IsValid()
      ensures a.IsValid()
    {
      if i in transitions then
        if j in transitions[i] then
          this
        else
          this
          .(transitions := transitions[i := transitions[i] + [j]] + (if j !in states then map[j := []] else map[]))
          .(states  := states + (if j in states then [] else [j]))
      else
        this
        .(transitions := transitions + map[i := [j]] + map[j := []])
        .(states := states + [i, j])
    }

    /**
      * Returns the number of states of the automaton.
      */
    function SSize(): nat
      requires this.IsValid()
    {
      |states|
    }

    /** Number of transitions of the automaton. */
    function TSize(xd: seq<T> := states): nat
      requires this.IsValid()
      requires (forall i : T :: i in xd ==> i in transitions)
    {
      if xd == [] then 0
      else
        assert xd[0] in states;
        |transitions[xd[0]]| + TSize(xd[1..])
    }

    /**
      * String representation of a state.
      */
    function ToString(t: T): string {
      toString(t)
    }

    /** Print to Dot format. */
    method {:print} ToDot()
      requires this.IsValid()
    {
      print "digraph G {\n";
      print "// Number of states: ", NatToString(SSize()), "\n";
      print "// Number of transitions : ", NatToString(TSize()), "\n";
      for i := 0 to |states| {
        print ToString(states[i]) + ";\n";
      }
      for i := 0 to |states| {
        for j := 0 to |transitions[states[i]]| {
          print ToString(states[i]) + " -> " + ToString(transitions[states[i]][j]) +
                "[label=\"" + NatToString(j) + "\"]"
                + ";\n";
        }
      }
      print "}\n";
    }

    ghost predicate IsValid() {
      && (forall i : T :: i in states <==> i in transitions)
    }
  }

  /** Attempt at defining a constraint on functions  */
  type WellDefined<!K(!new)> =
    f: (K, seq<K>) -> Option<K> | (forall x: K, xs: seq<K> {:triggers f(x, xs)} :: f(x, xs).Some? ==> f(x, xs).v in xs)
    witness ( (x: K, xs: seq<K>) => None)

  type WellDefined2<!K(!new)> =
    f: (K, seq<K>) -> Option<nat> | (forall x: K, xs: seq<K> {:triggers f(x, xs)} :: f(x, xs).Some? ==> f(x, xs).v < |xs|)
    witness ( (x: K, xs: seq<K>) => None)

  /**   For some reasons the following lemma cannot be proved. */
  lemma {:axiom} Foo101<K(!new)>(f: WellDefined<K>)
    ensures forall x: K, xs: seq<K> :: f(x, xs).Some? ==> f(x, xs).v in xs
  //   {
  //     assume forall x: K, xs: seq<K> :: f(x, xs).Some? ==> f(x, xs).v in xs;
  //   }

  lemma {:axiom} Foo102<K(!new)>(f: WellDefined2<K>)
    ensures forall x: K, xs: seq<K> :: f(x, xs).Some? ==> f(x, xs).v < |xs|
    {}
  //   {
  //     assume forall x: K, xs: seq<K> :: f(x, xs).Some? ==> f(x, xs).v in xs;
  //   }

  /**
    *   History of the DFS.
    *   @param init         The current state.
    *   @param visited      The set of visited states.
    *   @param path         The path from the root state to the current state.
    *   @param pathVisited  The set of visited states in the path.
    *
    *   @note               Ideally we would like to enforce that isCovered always 
    *                       returns a value in pathVisited. And use `WellDefined` instead.
    */
  datatype History<!K(!new,==)> = History(init: K, visited: seq<K>, path: seq<nat> := [], pathVisited: seq<K> := [], isCovered: WellDefined<K> := (x: K, xs: seq<K>) => None) {

    /** Add an state to the set of visited states. */
    function Add(k: K): (h: History<K>)
      requires this.IsValid()
      ensures h.IsValid()
    {
      if k in visited then
        this
      else
        this.(visited := visited + [k])
    }

    /** Retrieve index of item if it is visited. */
    function IndexOf(k: K, index: nat := 0): (r: Option<nat>)
      requires index <= |visited|
      requires k !in visited[..index]
      ensures r.None? || r.v < |visited|
      ensures k in visited ==> r.Some? && visited[r.v] == k
      decreases |visited| - index
    {
      if index == |visited| then None
      else if k == visited[index] then Some(index)
      else IndexOf(k, index + 1)
    }

    /**
      *  Update history when a child is visited.
      *  @param i  The index of the child in the list of successors.
      *  @param k  The child.
      */
    function AddToPathHistory(i: nat, k: K): (h: History<K>)
      requires this.IsValid()
      ensures h.IsValid()
    {
      this
      .Add(k)
      .(path := path + [i])
      .(pathVisited := pathVisited + [k])
    }

    /** initial prefix of path histories. */
    function PathHistoryInit(): (h: History<K>)
      requires this.IsValid()
      requires |path| >= 1
      ensures h.visited == this.visited
      ensures |h.path| == |this.path| - 1
      ensures h.IsValid()
    {
      this
      .(path := path[..|path| - 1])
      .(pathVisited := pathVisited[.. |pathVisited| - 1])
    }

    /**
      *  Ideally we woudl like to enforce isCovered to always return a value in the pathVisited.
      */
    function IsCovered(k: K): Option<K>
      requires this.IsValid()
    {
      if k in visited then Some(visited[IndexOf(k).v])
      else match isCovered(k, pathVisited)
           case None => None
           case Some(x) =>
             //  Force property of ValidFoo functions.
             Foo101(isCovered);
             Some(visited[IndexOf(x).v])
    }

    ghost predicate IsValid() {
      && |path| == |pathVisited|
      && (forall s:: s in pathVisited ==> s in visited)
    }
  }

  /** Depth first search g from s. 
    * @param g          A graph to unfold.
    * @param s          The initial node.
    * @param visited    Returns None if the node is not covered by any node in the history
    *                   and Some(x) if node x covers the node.
    * @param history    The history of visited nodes.
    * @param a          The automaton to build from the graph.
    * @param maxDepth   The maximum depth of the search.
    * @returns          The automaton and the history of visited nodes.
    */
  method DFS<T(!new)>(
    g: Graph<T>,
    s: T,
    history: History<T>,
    a: Auto<T>,
    maxDepth: nat := 0) returns (a': Auto<T>, h': History<T>)

    requires a.IsValid()
    requires history.IsValid()
    requires s in history.visited
    ensures a'.IsValid()
    ensures h'.IsValid()
    ensures |h'.path| == |history.path|

    decreases maxDepth
  {
    if maxDepth == 0 {
      //  stop the construction of the automaton.
      return a, history;
    }
    else {
      // DFS from s
      h' := history;
      a' := a;
      for i := 0 to |g.succ(s)|
        invariant a'.IsValid()
        invariant h'.IsValid()
        invariant |h'.path| == |history.path|
      {
        print "Unfolding ", s, " -> ", g.succ(s)[i], "\n";
        var n := h'.IsCovered(g.succ(s)[i]);
        if n.None? {
          var h1 := h'.AddToPathHistory(i, g.succ(s)[i]);
          //   print "a' = ", a'.addEdge(s, g.succ(s)[i]), "\n";
          a', h' := DFS(g, g.succ(s)[i], h1, a'.addEdge(s, g.succ(s)[i]), maxDepth - 1);
          h' := h'.PathHistoryInit();
          print a', "\n";
        } else {
          a' := a'.addEdge(s, n.v);
          //   print a', "\n";
        }
      }
    }
  }

}