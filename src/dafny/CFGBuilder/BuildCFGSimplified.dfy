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
include "../utils/Automata.dfy" 

module DFSSimple { 

  import opened MiscTypes 
  import opened Int
  import opened Automata 

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
    succ: T -> seq<T>,
    s: T,
    history: History<T>,
    a: ValidAuto<T>,
    maxDepth: nat := 0) returns (a': ValidAuto<T>, h': History<T>)  

    // requires a.IsValid2() 
    requires history.IsValid()
    requires s in history.visited
    // ensures a'.IsValid2()
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
      for i := 0 to |succ(s)|
        invariant a'.IsValid()
        invariant h'.IsValid()
        invariant |h'.path| == |history.path|
      {
        // print "Unfolding ", s, " -> ", succ(s)[i], "\n"; 
        var n := h'.IsCovered(succ(s)[i]);
        if n.None? {
          var h1 := h'.AddToPathHistory(i, succ(s)[i]);
          //   print "a' = ", a'.addEdge(s, succ(s)[i]), "\n";
          a', h' := DFS(succ, succ(s)[i], h1, a'.AddEdge(s, succ(s)[i]), maxDepth - 1);
          h' := h'.PathHistoryInit();
          print a', "\n";
        } else {
          a' := a'.AddEdge(s, n.v);
          //   print a', "\n";
        }
      }
    }
  }

}