/*
 * Copyright 2024 Franck Cassez
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

include "../utils/ProofObject.dfy"
include "../utils/int.dfy"
include "../utils/Hex.dfy"

/**
  * Given a sequence of segments with an unknown PC at the end,
  * resolve it.
  */
module PCResolver {

  import opened ProofObject
  import opened Int
  import opened Hex

  /**
    *    Build whole file 
    */
  function BuildDafnyModuleForResolver(path: seq<nat>, tgtPC: nat): string {
    var incl := "include \"./simpleCall.dfy\"\n";
    var imp := "import opened DafnyEVMProofObject\n";
    incl + imp + BuildDafnyResolver(path, tgtPC)
  }

  /**
    *   @param  path    A sequence of indices in seg.
    */
  function BuildDafnyResolver(path: seq<nat>, tgtPC: nat): string
  {
    // Build the tester
    var funcSig := "function TestPC(s0: EvmState.ExecutingState): (s':EvmState.State)\n";
    var funcRequires := "requires ExecuteFromTag_0.requires(s0)\n";
    var funcEnsures := "ensures s'.EXECUTING?\n" + "ensures s'.PC() == 0x" + NatToHex(tgtPC) + "\n";
    var funcBody := "{\n" + BuildPath(path) + "}\n";
    funcSig + funcRequires + funcEnsures + funcBody
  }

  /**   Build the body for execution of path.  */
  function BuildPath(xs: seq<nat>, body: string := "", counter: nat := 0): string
  {
    if |xs| == 0 then body + "s" + NatToString(counter) + "\n"
    else
      var p := BuildNextState(counter, xs[0]);
      BuildPath(xs[1..], body + p, counter + 1)
  }

  /**   Build computation of src + 1 state from src via tag_segNum. */
  function BuildNextState(src : nat, segNum: nat): string {
    "var s" +  NatToString(src + 1) +
    " := ExecuteFromTag_" + NatToString(segNum) +
    "(s" + NatToString(src) + ");\n"
  }

}