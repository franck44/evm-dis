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

include "./CFGraph.dfy"
include "./EVMObject.dfy"
include "./State.dfy"
include "MiscTypes.dfy"

/**
  * Provides Depth-First-Search history.
  */
module DFS {

  import opened CFGraph
  import opened EVMObject
  import opened State
  import opened MiscTypes

  /**  DFS current path history. */
  datatype PathHistory =
    PathHistory(seen: seq<CFGNode>, seenPCs: seq<nat>, path: seq<bool>) {

    /** The history should be well-formed  */
    predicate IsConsistent(c: EVMObj, s: ValidState) {
      && |seen| == |seenPCs| == |path| + 1
         //   && s in seenStates
      && (forall k:: 0 <= k < |seen| ==> seen[k].id == path[..k])
      && (forall k:: 0 <= k < |seen| ==> seen[k].seg.Some?)
      && (forall k:: k in seen && k.seg.Some? ==> k.seg.v < |c.xs|)
      && (s.PC() == seenPCs[|seenPCs| - 1])
      && (forall k:: 0 <= k < |seen| ==> seenPCs[k] == c.xs[seen[k].seg.v].StartAddress())
    }
  }

  const DEFAULT_PATH_HISTORY :=
    PathHistory([CFGNode([], Some(0))], [0], [])

  /** DFS entire search history. */
  datatype DFSHistory =
    DFSHistory(visitedStates: map<AState, CFGNode>) {


    /** The history should be well-formed  */
    predicate IsConsistent(c: EVMObj, s: ValidState) {
      && s in visitedStates
      && (forall s:: s in visitedStates && visitedStates[s].seg.Some? ==> visitedStates[s].seg.v < |c.xs|)
    }
  }

  const DEFAULT_DFS_HISTORY :=
    DFSHistory(map[DEFAULT_VALIDSTATE := CFGNode([], Some(0))])


  /**  CFG computation  */
  //   datatype CFGComputation = CFGComputation(
  //     grph: BoolCFGraph,
  //     states:  map<AState, CFGNode>) {

  //     function Graph(): BoolCFGraph {
  //       grph
  //     }

  //     function States(): map<AState, CFGNode> {
  //       states
  //     }
  //   }


}