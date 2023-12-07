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


include "../../../src/dafny/utils/StackElement.dfy"
include "../../../src/dafny/utils/State.dfy"
include "../../../src/dafny/utils/Instructions.dfy"
include "../../../src/dafny/disassembler/OpcodeDecoder.dfy"
include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/LinSegments.dfy"
include "../../../src/dafny/prettyprinters/Pretty.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/CFGBuilder/BuildCFG.dfy"
/**
  * Test correct computation of next State.
  * 
  */ 
module NextStateTests { 

  import opened MiscTypes
  import opened OpcodeDecoder
  import opened EVMConstants
  import opened Instructions
  import Int
  import opened State
  import opened StackElement
  import opened BinaryDecoder
  import opened PrettyPrinters
  import opened Splitter
  import opened BuildCFGraph 
  import opened LinSegments

  /** Arithmetic instruction. Proofs. */


  /**   RJUMP (not implemented an result in Error). */
  method {:test} Test1()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(RJUMPI));
      expect i.NextState(s, [], true).Error?;
      expect i.NextState(s, [], false).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(RJUMPV));
      expect i.NextState(s, [], true).Error?;
      expect i.NextState(s, [], false).Error?;
    }
  }

  
}