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
    *   @param  p       The part thathas already been disassembled.
    *   @param  next    The next available address to store the instructions.
    */
  function {:tailrec} Disassemble(s: string, p: seq<ValidInstruction> := [], next: nat := 0): seq<ValidInstruction>
    decreases |s|
  {
    if |s| == 0 then
      p
    else if |s| == 1 then
      p + [Instruction(Decode(INVALID), s, next)]
    else
      assert |s| >= 2;
      // Try to decode next instruction
      match HexToU8(s[..2])
      case None => p + [Instruction(Decode(INVALID), "'" + s[..2] + "' is not a known opcode", next)]
      case Some(v) =>
        //  Try to read parameters of opcode
        var op := Decode(v);
        if op.Args() > 0 then
          //  try to skip 2 * Args()
          if |s[2..]| < 2 * op.Args() || !IsHexString(s[2..][..2 * op.Args()]) then
            p + [Instruction(Decode(INVALID), "not enough arguments for opcode " + op.name, next)]
          else
            assert |s[2..][2 * op.Args()..]| < |s|;
            // assert 
            Disassemble(s[2..][2 * op.Args()..], p + [Instruction(op, s[2..][..2 * op.Args()], next)], next + 1 + op.Args() )
        else
          Disassemble(s[2..], p + [Instruction(op, [], next)], next + 1)
  }

  predicate IsHexString(s: string) 
    // ensures forall 
  {
    forall k :: 0 <= k < |s| ==> IsHex(s[k])
  }

  function {:tailrec} DisassembleU8(s: seq<u8>, p: seq<ValidInstruction> := [], next: nat := 0): seq<ValidInstruction>
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
          p + [Instruction(Decode(INVALID))]
        else
          assert |s[1..][op.Args()..]| < |s|;
          DisassembleU8(s[1..][op.Args()..], p + [Instruction(op, HexHelper(s[1..][..op.Args()]), next)], next + 1 + op.Args())
      else
        DisassembleU8(s[1..], p + [Instruction(op, [], next)], next + 1)
  }

  function {:tailrecursion true} HexHelper(s: seq<u8>): string
    requires |s| <= 32
    ensures |HexHelper(s)| % 2 == 0
    ensures |HexHelper(s)| == 2 * |s| <= 64
    ensures IsHexString(HexHelper(s))
  {
    if |s| == 0 then ""
    else U8ToHex(s[0]) + HexHelper(s[1..])
  }

  function {:tailrecursion true} StringToU8Helper(s: string, decoded: seq<Int.u8> := []): (r : Option<seq<Int.u8>>)
    // requires
  {
    if |s| == 0 then Some(decoded)
    else if |s| == 1 then
      match HexToU8("0" + [s[0]])
      case Some(v) => Some(decoded + [v as Int.u8])
      case None => None
    else
      match HexToU8(s[0..2])
      case Some(v) => StringToU8Helper(s[2..], decoded + [v as Int.u8])
      case None => None
  }

  lemma foo(s: string, d: seq<Int.u8>)
    ensures StringToU8Helper(s, d).Some? ==> |StringToU8Helper(s, d).v| <= |s|/2 + 1 + |d|
  {

  }

  lemma foo101(s: string)
    ensures  StringToU8Helper(s).Some? ==> |StringToU8Helper(s).v| <= |s|/2 + 1
  {
    foo(s, []);
  }
}

