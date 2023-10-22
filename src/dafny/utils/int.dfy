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

module Int {

    // const TWO_7   : int := 0x0_80
    const TWO_8   : int := 0x1_00
    // const TWO_15  : int := 0x0_8000
    const TWO_16  : int := 0x1_0000
    // const TWO_24  : int := 0x1_0000_00
    // const TWO_31  : int := 0x0_8000_0000
    const TWO_32  : int := 0x1_0000_0000
    // const TWO_40  : int := 0x1_0000_0000_00
    // const TWO_48  : int := 0x1_0000_0000_0000
    // const TWO_56  : int := 0x1_0000_0000_0000_00
    // const TWO_63  : int := 0x0_8000_0000_0000_0000
    const TWO_64  : int := 0x1_0000_0000_0000_0000
    // const TWO_72  : int := 0x1_0000_0000_0000_0000_00
    // const TWO_80  : int := 0x1_0000_0000_0000_0000_0000
    // const TWO_88  : int := 0x1_0000_0000_0000_0000_0000_00
    // const TWO_96  : int := 0x1_0000_0000_0000_0000_0000_0000
    // const TWO_104 : int := 0x1_0000_0000_0000_0000_0000_0000_00
    // const TWO_112 : int := 0x1_0000_0000_0000_0000_0000_0000_0000
    // const TWO_120 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_127 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000
    const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000
    // const TWO_136 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_144 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000
    // const TWO_152 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_160 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    // const TWO_168 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_176 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    // const TWO_184 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_192 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    // const TWO_200 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_208 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    // const TWO_216 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_224 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    // const TWO_232 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_240 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    // const TWO_248 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_00
    // const TWO_255 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

    // Signed Integers
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

    newtype{:nativeType "byte"} u8 = i:nat    | 0 <= i <= MAX_U8
    newtype{:nativeType "ushort"} u16 = i:nat | 0 <= i <= MAX_U16
    newtype{:nativeType "uint"} u32 = i:nat   | 0 <= i <= MAX_U32
    newtype{:nativeType "ulong"} u64 = i:nat  | 0 <= i <= MAX_U64
    newtype u128 = i:nat | 0 <= i <= MAX_U128
    newtype u256 = i:nat | 0 <= i <= MAX_U256

}