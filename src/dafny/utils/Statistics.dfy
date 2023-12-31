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

include "./int.dfy"

/**
  *  Provides statistics for the DFS.
  */
module Statistics {

  import Int

  /**   Statistics for the DFS. */
  datatype Stats = Stats(maxDepthReached: bool := false, visitedStates: nat := 0, wPreInvSuccess: nat := 0, errorState: nat := 0, nonMinimisedSize : (nat, nat) := (0,0)) {

    /** Set the indicator that maxDepth is reached to true. */
    function SetMaxDepth(): Stats {
      this.(maxDepthReached := true)
    }

    /** Increment the number of visited states. */
    function IncVisited(): Stats {
      this.(visitedStates := this.visitedStates + 1)
    }

    /** Increment the count of successful WPre checks. */
    function IncWpre(): Stats {
      this.(wPreInvSuccess := this.wPreInvSuccess + 1)
    }

    function IncError(): Stats {
      this.(errorState := this.errorState + 1)
    }

    /** Pretty-print the statistics. */
    function PrettyPrint(): string {
      "// MaxDepth reached:" + (if maxDepthReached then "true" else "false") +"\n"
      + "// ErrorStates reached:" + Int.NatToString(errorState) + "\n"
      + "// States seen:" + Int.NatToString(visitedStates) + "\n"
      + "// WPre success:" + Int.NatToString(wPreInvSuccess) + "\n"
    }
  }

  /** Default value for Stats. */
  const DEFAULT_STATS := Stats()

}