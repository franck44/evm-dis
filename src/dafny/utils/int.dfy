/*
 * Copyright 2022 ConsenSys Software Inc.
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

module Int {

  import opened MiscTypes

  const TWO_4   : nat := 0x10
  // const TWO_7   : nat := 0x0_80
  const TWO_8   : nat := 0x1_00
  // const TWO_15  : nat := 0x0_8000
  const TWO_16  : nat := 0x1_0000
  // const TWO_24  : nat := 0x1_0000_00
  // const TWO_31  : nat := 0x0_8000_0000
  const TWO_32  : nat := 0x1_0000_0000
  // const TWO_40  : nat := 0x1_0000_0000_00
  // const TWO_48  : nat := 0x1_0000_0000_0000
  // const TWO_56  : nat := 0x1_0000_0000_0000_00
  // const TWO_63  : nat := 0x0_8000_0000_0000_0000
  const TWO_64  : nat := 0x1_0000_0000_0000_0000
  // const TWO_72  : nat := 0x1_0000_0000_0000_0000_00
  // const TWO_80  : nat := 0x1_0000_0000_0000_0000_0000
  // const TWO_88  : nat := 0x1_0000_0000_0000_0000_0000_00
  // const TWO_96  : nat := 0x1_0000_0000_0000_0000_0000_0000
  // const TWO_104 : nat := 0x1_0000_0000_0000_0000_0000_0000_00
  // const TWO_112 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000
  // const TWO_120 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_127 : nat := 0x0_8000_0000_0000_0000_0000_0000_0000_0000
  const TWO_128 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000
  // const TWO_136 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_144 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000
  // const TWO_152 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_160 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
  // const TWO_168 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_176 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
  // const TWO_184 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_192 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
  // const TWO_200 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_208 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
  // const TWO_216 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_224 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
  // const TWO_232 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_240 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
  // const TWO_248 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
  // const TWO_255 : nat := 0x0_8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
  const TWO_256 : nat := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

  // Signed nategers
  // const MIN_I8   : int := -TWO_7
  // const MAX_I8   : int :=  TWO_7 - 1
  // const MIN_I16  : int := -TWO_15
  // const MAX_I16  : int :=  TWO_15 - 1
  // const MIN_I32  : int := -TWO_31
  // const MAX_I32  : int :=  TWO_31 - 1
  // const MIN_I64  : int := -TWO_63
  // const MAX_I64  : int :=  TWO_63 - 1
  // const MIN_I128 : int := -TWO_127
  // const MAX_I128 : int :=  TWO_127 - 1
  // const MIN_I256 : int := -TWO_255
  // const MAX_I256 : int :=  TWO_255 - 1

  // newtype{:nativeType "sbyte"} i8 = i:int   | MIN_I8 <= i <= MAX_I8
  // newtype{:nativeType "short"} i16 = i:int  | MIN_I16 <= i <= MAX_I16
  // newtype{:nativeType "int"}   i32 = i:int  | MIN_I32 <= i <= MAX_I32
  // newtype{:nativeType "long"}  i64 = i:int  | MIN_I64 <= i <= MAX_I64
  // newtype i128 = i:int | MIN_I128 <= i <= MAX_I128
  // newtype i256 = i:int | MIN_I256 <= i <= MAX_I256

  // Unsigned Integers
  const MAX_U8 : nat :=  TWO_8 - 1
  const MAX_U16 : nat := TWO_16 - 1
  const MAX_U32 : nat := TWO_32 - 1
  const MAX_U64 : nat := TWO_64 - 1
  const MAX_U128: nat := TWO_128 - 1
  const MAX_U256: nat := TWO_256 - 1

  newtype u8 = i:nat | 0 <= i <= MAX_U8
  newtype u16 = i:nat | 0 <= i <= MAX_U16
  newtype u32 = i:nat | 0 <= i <= MAX_U32
  newtype u64 = i:nat | 0 <= i <= MAX_U64
  newtype u128 = i:nat | 0 <= i <= MAX_U128
  newtype u256 = i:nat | 0 <= i <= MAX_U256

  //  Helpers
  // Compute absolute value
  function Abs(x: int) : nat {
    if x >= 0 then x else -x
  }

  // Determine maximum of two u256 integers.
  function Max(i1: int, i2: int) : int {
    if i1 >= i2 then i1 else i2
  }

  // Determine maximum of two u256 integers.
  function Min(i1: int, i2: int) : int {
    if i1 < i2 then i1 else i2
  }

  function NatToString(n: nat): string
  {
    if n < 10 then [DigitToString(n)]
    else NatToString(n / 10) + [DigitToString(n % 10)]
  }

  function IntToString(n: int): string
  {
    if n == 0 then "0"
    else if n > 0 then "+" + NatToString(n)
    else "-" + NatToString(-n)
  }

  /**
    *  Encode a decimal number into a Hex.
    */
  function DigitToString(n: nat): char
    requires 0 <= n < 10
    ensures '0' <= DigitToString(n) <= '9'
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
  }

  /**
    *  Decode a char into a digit.
    */
  function CharToDigit(c: char): (r: Option<nat>)
    ensures r.Some? ==> 0 <= r.v <= 9
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
    case _ => None
  }

  predicate IsNatNumber(s: string)
    requires |s| >= 1
    ensures IsNatNumber(s) <==> forall k:: 0 <= k < |s| ==> CharToDigit(s[k]).Some?
  {
    if |s| == 1 then CharToDigit(s[0]).Some?
    else
      match CharToDigit(s[0])
      case Some(v) => IsNatNumber(s[1..])
      case None => false
  }


  /**   Convert a string to a Nat. */
  function {:tailrecursion false} StringToNat(s: string, lastVal: nat := 0): nat
    requires |s| > 0
    requires IsNatNumber(s)
  {
    if |s| == 1 then CharToDigit(s[0]).v
    else
      var v := CharToDigit(s[|s| - 1]).v;
      v + 10 * StringToNat(s[..|s| - 1])
  }

}