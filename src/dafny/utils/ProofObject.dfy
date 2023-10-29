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
include "../utils/LinSegments.dfy"
// include "../utils/LinSegments.dfy"

/**
  *  Provides proof objects types.
  */
module ProofObject {

  import opened MiscTypes
  import opened LinSegments
  import opened Instructions
  

  /**
    *   sp.Keys contaisn the tracked/needed stack positions AFTER
    *   the last instruction.
    *   They are either a known destination (string) or a stack element
    *   of the incoming state.
    */
  datatype StackResolver = StackResolver(sp: map<nat, Either<string, nat>>)
  {

  }

    
  /**
    *   Either a segment terminating with a JUMP or a segment terminating with a STOP/RETURN/REVERT
    */
  datatype ProofObj =
    |  JUMP(s: ValidLinSeg, wpOp: nat, wpCap: nat, tgt: Either<seq<char>, nat>, stacks: StackResolver := StackResolver(map[]))
    |   CONT(s: ValidLinSeg, wpOp: nat, wpCap: nat, stacks: StackResolver := StackResolver(map[])) 
    |  TERMINAL(s: ValidLinSeg, wpOp: nat, wpCap: nat, stacks: StackResolver := StackResolver(map[]))
  {
    predicate IsValid() {
         match this 
            case JUMP(_, _, _, _, _) => s.JUMPSeg? || s.JUMPISeg?
            case CONT(_, _, _, _) => s.CONTSeg? 
            case TERMINAL(_, _, _, _) => true  
    } 

    /**
      * The addresses of the JUMPDEST instructions.
      */
    function CollectJumpDest(): seq<nat>
    {
      s.CollectJumpDest()
    }

    /**
      * The net stack effect of a sequence of instructions in a linear segment.
      * @note   The number of pushes minus the number of pops.
      */
    function StackEffect(): int {
      s.StackEffect() 
    }
  }

}

