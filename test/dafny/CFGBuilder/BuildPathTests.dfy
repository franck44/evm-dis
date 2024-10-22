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

include "../../../src/dafny/CFGBuilder/PCResolver.dfy"

/**
  * Test Dafny function generation.
  * 
  */
module BuildPathTests { 

  import opened PCResolver

  /** From state 2 to state 3 via tag_4 */
  method {:test} {:verify true} Test1()
  {
    var r := BuildNextState(2, 4);
    expect r == "var s3 := ExecuteFromTag_4(s2);\n";
  }

  /** From state 0 to state 1 via tag_2 */
  method {:test} {:verify true} Test2()
  {
    var r := BuildNextState(0, 2);
    expect r == "var s1 := ExecuteFromTag_2(s0);\n";

  }

  /** Empty path, should result in last encountered state i.e. s0. */
  method {:test} {:verify true} Test10()
  {
    var path1 := [];
    var r1 := BuildPath(path1);
    expect r1 == "s0\n";

  }

  /** Execute tag2 then tag_3 from s0. */
  method {:test} {:verify true} Test11()
  {
    var path1 := [2, 3];
    var r1 := BuildPath(path1);
    expect r1 == "var s1 := ExecuteFromTag_2(s0);\nvar s2 := ExecuteFromTag_3(s1);\ns2\n";
  }

  /** Complete function generation */
  method {:test} {:verify true} Test20()
  {
    var path := [];
    var r1 := BuildDafnyResolver(path, 0x10);
    expect r1 ==
           "function TestPC(s0: EvmState.ExecutingState): (s':EvmState.State)\n"
           + "requires ExecuteFromTag_0.requires(s0)\n"
           + "ensures s'.EXECUTING?\n" + "ensures s'.PC() == 0x10\n"
           + "{\n"
           +  "s0\n"
           + "}\n"
      ;
  }

  method {:test} {:verify true} Test21()
  {
    var path := [2, 3];
    var r1 := BuildDafnyResolver(path, 0x24);
    expect r1 ==
           "function TestPC(s0: EvmState.ExecutingState): (s':EvmState.State)\n"
           + "requires ExecuteFromTag_0.requires(s0)\n"
           + "ensures s'.EXECUTING?\n" + "ensures s'.PC() == 0x24\n"
           + "{\n"
           + "var s1 := ExecuteFromTag_2(s0);\n"
           + "var s2 := ExecuteFromTag_3(s1);\n"
           +  "s2\n"
           + "}\n"
      ;
  }

}

