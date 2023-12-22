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

include "./OpcodeDecoder.dfy"
include "../utils/Hex.dfy"
include "../utils/Instructions.dfy"
include "../utils/MiscTypes.dfy"

/**
  *  Provides binary decoder.
  */
module BinaryDecoder {

  import opened OpcodeDecoder
  import opened EVMOpcodes
  import opened Hex
  import opened Int
  import opened EVMConstants
  import opened Instructions
  import opened MiscTypes

  /**
    *  Disassemble a string into a sequence of instructions.
    *
    *   @param  s       The string that remains to be disassembled.
    *   @param  p       The part that has already been disassembled.
    *   @param  next    The next available address to store the instructions.
    *   @returns        A seq of valid instructions that correspond to `s`.
    *
    *   @note           Some of the instructions may be instances of INVALID.
    */
  function {:tailrecursion true} Disassemble(s: string, p: seq<ValidInstruction> := [], next: nat := 0): (r: seq<ValidInstruction>)
    requires forall i:: 0 <= i < |p| ==> p[i].address < next
    requires forall i, i':: 0 <= i < i' < |p| ==> p[i].address < p[i'].address
    ensures forall i, i':: 0 <= i < i' < |r| ==> r[i].address < r[i'].address
    decreases |s|
  {
    if |s| == 0 then
      p
    else if |s| == 1 then
      // One character is not enough to make an instruction
      p + [Instruction(Decode(INVALID), "Odd number of characters ending in " + s, next)]
    else
      assert |s| >= 2;
      // Try to decode next instruction
      match HexToU8(s[..2])
      case None =>
        //  first two chars of s are not Hex
        p + [Instruction(Decode(INVALID), "'" + s[..2] + "' is not an Hex number", next)]
      case Some(v) =>
        //  Good! Got an Hex number. Decode it. Results in INVALID if not a known opcode.
        var op := Decode(v);
        //  Try to read the parameters of opcode
        if op.Args() > 0 then
          //  try to skip 2 * Args() as each arg needs 2 Hex chars
          if |s[2..]| < 2 * op.Args() || !IsHexString(s[2..][..2 * op.Args()]) then
            //  Not enough arguments
            p + [Instruction(Decode(INVALID), "not enough arguments for opcode " + op.name, next)]
          else
            //  Good. There is enough arguments.
            assert |s[2..][2 * op.Args()..]| < |s|;
            Disassemble(s[2..][2 * op.Args()..], p + [Instruction(op, s[2..][..2 * op.Args()], next)], next + 1 + op.Args() )
        else
          //  No argument for this opcode, proceed to next one
          Disassemble(s[2..], p + [Instruction(op, [], next)], next + 1)
  }

  /**
    *   Disassemble seq of bytes. 
    *   @note   This is a simploified version of Disassemble where we have u8 instead
    *           of strings.
    *   @note   Used in tests, rather than disassembling hex, we can write tests
    *           code as seq of bytes directly.
    */
  function {:tailrecurseion true} DisassembleU8(s: seq<u8>, p: seq<ValidInstruction> := [], next: nat := 0): (r: seq<ValidInstruction>)
    requires forall i:: 0 <= i < |p| ==> p[i].address < next
    requires forall i, i':: 0 <= i < i' < |p| ==> p[i].address < p[i'].address
    ensures forall i, i':: 0 <= i < i' < |r| ==> r[i].address < r[i'].address
    decreases |s|
  {
    if |s| == 0 then
      p
    else
      //  Try to read parameters of opcode
      var op := Decode(s[0]);
      if op.Args() > 0 then
        //  try to skip Args()
        if |s[1..]| < op.Args() then
          p + [Instruction(Decode(INVALID), "not enough arguments for opcode " + op.name, next)]
        else
          assert |s[1..][op.Args()..]| < |s|;
          DisassembleU8(s[1..][op.Args()..], p + [Instruction(op, HexHelper(s[1..][..op.Args()]), next)], next + 1 + op.Args())
      else
        DisassembleU8(s[1..], p + [Instruction(op, [], next)], next + 1)
  }

}

