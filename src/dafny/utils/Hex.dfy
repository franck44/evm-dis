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


include "./MiscTypes.dfy"
include "./int.dfy"

/**
  * Provides Hex string to u8 decoder. 
  */
module Hex {

  import opened MiscTypes
  import Int

  /**
    *   Decode a 2-digit hex number into a u8.
    *   @param  s   The string to decode
    *   @returns    The value in decimal of the 2-char hex number.
    *   @example    `0f` or 0F` is 15, `a1` is 10*16 + 1 = 161. 
    */
  function HexToU8(s: string): Option<Int.u8>
    requires |s| == 2
  {
    match (HexVal(s[0]), HexVal(s[1]))
    case (None, _) => None
    case (_, None) => None
    case (Some(v1), Some(v2)) => Some(16 * v1 + v2)
  }

  /**
    *  Decode an Hex digit.
    */
  function HexVal(c: char): Option<Int.u8>
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


}