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


include "./MiscTypes.dfy"
include "./int.dfy"

/**
  * Provides Hex string to nat. 
  */
module Hex {

  import opened MiscTypes
  import opened Int

  /** 
    *   @param  s   A string (seq of chars).
    *   @returns    true iff every char is within 0..f.
    */
  predicate IsHexString(s: string)
  {
    forall k :: 0 <= k < |s| ==> IsHex(s[k])
  }

  /**
    *   Decode a 2-digit hex number into a u8.
    *   @param  s   The string to decode
    *   @returns    The value in decimal of the 2-char hex number.
    *   @example    `0f` or 0F` is 15, `a1` is 10*16 + 1 = 161. 
    */
  function HexToU8(s: string): Option<u8>
    requires |s| == 2
  {
    match (HexVal(s[0]), HexVal(s[1]))
    case (None, _) => None
    case (_, None) => None
    case (Some(v1), Some(v2)) => Some((TWO_4 * v1 as nat + v2 as nat) as u8)
  }

  function HexToU16(s: string): Option<u16>
    requires |s| == 4
  {
    match (HexToU8(s[..2]), HexToU8(s[2..]))
    case (None, _) => None
    case (_, None) => None
    case (Some(v1), Some(v2)) =>
      Some(((TWO_8 * v1 as nat + v2 as nat) as u16))
  }

  function HexToU32(s: string): Option<u32>
    requires |s| == 8
  {
    match (HexToU16(s[..4]), HexToU16(s[4..]))
    case (None, _) => None
    case (_, None) => None
    case (Some(v1), Some(v2)) =>
      Some(((TWO_16 * v1 as nat + v2 as nat) as u32))
  }

  function HexToU64(s: string): Option<u64>
    requires |s| == 16
    ensures (forall k:: 0 <= k < |s| ==> IsHex(s[k])) ==> HexToU64(s).Some?
  {
    match (HexToU32(s[..8]), HexToU32(s[8..]))
    case (None, _) => None
    case (_, None) => None
    case (Some(v1), Some(v2)) =>
      Some(((TWO_32 * v1 as nat + v2 as nat) as u64))
  }

  function HexToU128(s: string): Option<u128>
    requires |s| == 32
    ensures (forall k:: 0 <= k < |s| ==> IsHex(s[k])) ==> HexToU128(s).Some?
  {
    match (HexToU64(s[..16]), HexToU64(s[16..]))
    case (None, _) => None
    case (_, None) => None
    case (Some(v1), Some(v2)) =>
      Some(((TWO_64 * v1 as nat + v2 as nat) as u128))
  }

  function HexToU256(s: string): Option<u256>
    requires |s| == 64
    ensures (forall k:: 0 <= k < |s| ==> IsHex(s[k])) ==> HexToU256(s).Some?
  {
    match (HexToU128(s[..32]), HexToU128(s[32..]))
    case (None, _) => None
    case (_, None) => None
    case (Some(v1), Some(v2)) =>
      Some(((TWO_128 * v1 as nat + v2 as nat) as u256))
  }

  // Helpers to convert uint into hexadecimal strings.

  function U8ToHex(n: u8): string
    ensures |U8ToHex(n)| == 2
  {
    [DecToHex(n as nat / TWO_4)] + [DecToHex(n as nat % TWO_4)]
  }

  /**   Convert a seq of bytes into a string. */
  function {:tailrecursion true} HexHelper(s: seq<u8>): string
    requires |s| <= 32
    ensures |HexHelper(s)| % 2 == 0
    ensures |HexHelper(s)| == 2 * |s| <= 64
    ensures IsHexString(HexHelper(s))
  {
    if |s| == 0 then ""
    else U8ToHex(s[0]) + HexHelper(s[1..])
  }


  function U16ToHex(n: u16): string
    ensures |U16ToHex(n)| == 4
  {
    U8ToHex((n as nat / TWO_8) as u8) + U8ToHex((n as nat % TWO_8) as u8)
  }

  function U32ToHex(n: u32): string
    ensures |U32ToHex(n)| == 8
  {
    U16ToHex((n as nat / TWO_16) as u16) + U16ToHex((n as nat % TWO_16) as u16)
  }

  function U64ToHex(n: u64): string
    ensures |U64ToHex(n)| == 16
  {
    U32ToHex((n as nat / TWO_32) as u32) + U32ToHex((n as nat % TWO_32) as u32)
  }

  function U128ToHex(n: u128): string
    ensures |U128ToHex(n)| == 32
  {
    U64ToHex((n as nat / TWO_64) as u64) + U64ToHex((n as nat % TWO_64) as u64)
  }

  function U256ToHex(n: u256): string
    ensures |U256ToHex(n)| == 64
  {
    U128ToHex((n as nat / TWO_128) as u128) + U128ToHex((n as nat % TWO_128) as u128)
  }

  function NatToHex(n: nat): string
  {
    if n < 16 then [DecToHex(n)]
    else NatToHex(n / 16) + [DecToHex(n % 16)]
  }

  // From hex to Decimal and back.

  /**
    *  Decode an Hex digit.
    */
  function HexVal(c: char): Option<u8>
    ensures IsHex(c) ==> HexVal(c).Some?
    ensures HexVal(c).Some? ==> HexVal(c).v <= 15
  {
    match c
    case '0' => Some(0)
    case '1' => Some(1)
    case '2' => Some(2)
    case '3' => Some(3)
    case '4' => Some(4)
    case '5' => Some(5)
    case '6' => Some(6)
    case '7' => Some(7)
    case '8' => Some(8)
    case '9' => Some(9)
    case 'a' => Some(10)
    case 'A' => Some(10)
    case 'b' => Some(11)
    case 'B' => Some(11)
    case 'c' => Some(12)
    case 'C' => Some(12)
    case 'd' => Some(13)
    case 'D' => Some(13)
    case 'e' => Some(14)
    case 'E' => Some(14)
    case 'f' => Some(15)
    case 'F' => Some(15)
    case _ => None
  }

  /**
    *  Encode a decimal number into a Hex.
    */
  function DecToHex(n: nat): char
    requires 0 <= n < 16
    ensures '0' <= DecToHex(n) <= '9' || 'a' <= DecToHex(n) <= 'f'
  {
    match n
    case 0 => '0'
    case 1 => '1'
    case 2 => '2'
    case 3 => '3'
    case 4 => '4'
    case 5 => '5'
    case 6 => '6'
    case 7 => '7'
    case 8 => '8'
    case 9 => '9'
    case 10 => 'a'
    case 11 => 'b'
    case 12 => 'c'
    case 13 => 'd'
    case 14 => 'e'
    case 15 => 'f'
  }

  /**   Whether a character is a Hex symbol. */
  predicate IsHex(c: char)
  {
    '0' <= c <= '9' || 'a' <= c <= 'f' || 'A' <= c <= 'F'
  }

}