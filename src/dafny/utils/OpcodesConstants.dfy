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

include "./int.dfy"

/**
  *  Provides EVM Opcodes.
  */
module EVMConstants {

  import opened Int

  //    Constants. Borrowed from Dafny-EVM project.

  // 0s: Stop and Arithmetic Operations
  const STOP: u8       := 0x0
  const ADD: u8        := 0x01
  const MUL: u8        := 0x02
  const SUB: u8        := 0x03
  const DIV: u8        := 0x04
  const SDIV: u8       := 0x05
  const MOD: u8        := 0x06
  const SMOD: u8       := 0x07
  const ADDMOD: u8     := 0x08
  const MULMOD: u8     := 0x09
  const EXP: u8        := 0x0a
  const SIGNEXTEND: u8 := 0x0b
  // 10s: Comparison & Bitwise Logic Operations
  const LT: u8     := 0x10
  const GT: u8     := 0x11
  const SLT: u8    := 0x12
  const SGT: u8    := 0x13
  const EQ: u8     := 0x14
  const ISZERO: u8 := 0x15
  const AND: u8    := 0x16
  const OR: u8     := 0x17
  const XOR: u8    := 0x18
  const NOT: u8    := 0x19
  const BYTE: u8   := 0x1a
  const SHL: u8    := 0x1b
  const SHR: u8    := 0x1c
  const SAR: u8    := 0x1d
  // 20s: SHA3
  const KECCAK256: u8 := 0x20
  // 30s: Environment Information
  const ADDRESS: u8        := 0x30
  const BALANCE: u8        := 0x31
  const ORIGIN: u8         := 0x32
  const CALLER: u8         := 0x33
  const CALLVALUE: u8      := 0x34
  const CALLDATALOAD: u8   := 0x35
  const CALLDATASIZE: u8   := 0x36
  const CALLDATACOPY: u8   := 0x37
  const CODESIZE: u8       := 0x38
  const CODECOPY: u8       := 0x39
  const GASPRICE: u8       := 0x3a
  const EXTCODESIZE: u8    := 0x3b
  const EXTCODECOPY: u8    := 0x3c
  const RETURNDATASIZE: u8 := 0x3d
  const RETURNDATACOPY: u8 := 0x3e
  const EXTCODEHASH: u8    := 0x3f
  // 40s: Block Information
  const BLOCKHASH: u8   := 0x40
  const COINBASE: u8    := 0x41
  const TIMESTAMP: u8   := 0x42
  const NUMBER: u8      := 0x43
  const DIFFICULTY: u8  := 0x44
  const GASLIMIT: u8    := 0x45
  const CHAINID: u8     := 0x46
  const SELFBALANCE: u8 := 0x47
  const BASEFEE: u8     := 0x48
  // 50s: Stack, Memory Storage and Flow Operations
  const POP: u8      := 0x50
  const MLOAD: u8    := 0x51
  const MSTORE: u8   := 0x52
  const MSTORE8: u8  := 0x53
  const SLOAD: u8    := 0x54
  const SSTORE: u8   := 0x55
  const JUMP: u8     := 0x56
  const JUMPI: u8    := 0x57
  const PC: u8       := 0x58
  const MSIZE: u8    := 0x59
  const GAS: u8      := 0x5a
  const JUMPDEST: u8 := 0x5b
  const RJUMP: u8    := 0x5c  // EIP-4200
  const RJUMPI: u8   := 0x5d // EIP-4200
  const RJUMPV: u8   := 0x5e // EIP-4200
  const PUSH0: u8    := 0x5f // EIP-3855
  // 60s & 70s: Push Operations
  const PUSH1: u8 := 0x60
  const PUSH2: u8 := 0x61
  const PUSH3: u8 := 0x62
  const PUSH4: u8 := 0x63
  const PUSH5: u8 := 0x64
  const PUSH6: u8 := 0x65
  const PUSH7: u8 := 0x66
  const PUSH8: u8 := 0x67
  const PUSH9: u8 := 0x68
  const PUSH10: u8 := 0x69
  const PUSH11: u8 := 0x6a
  const PUSH12: u8 := 0x6b
  const PUSH13: u8 := 0x6c
  const PUSH14: u8 := 0x6d
  const PUSH15: u8 := 0x6e
  const PUSH16: u8 := 0x6f
  const PUSH17: u8 := 0x70
  const PUSH18: u8 := 0x71
  const PUSH19: u8 := 0x72
  const PUSH20: u8 := 0x73
  const PUSH21: u8 := 0x74
  const PUSH22: u8 := 0x75
  const PUSH23: u8 := 0x76
  const PUSH24: u8 := 0x77
  const PUSH25: u8 := 0x78
  const PUSH26: u8 := 0x79
  const PUSH27: u8 := 0x7a
  const PUSH28: u8 := 0x7b
  const PUSH29: u8 := 0x7c
  const PUSH30: u8 := 0x7d
  const PUSH31: u8 := 0x7e
  const PUSH32: u8 := 0x7f
  // 80s: Duplication Operations
  const DUP1: u8 := 0x80
  const DUP2: u8 := 0x81
  const DUP3: u8 := 0x82
  const DUP4: u8 := 0x83
  const DUP5: u8 := 0x84
  const DUP6: u8 := 0x85
  const DUP7: u8 := 0x86
  const DUP8: u8 := 0x87
  const DUP9: u8 := 0x88
  const DUP10: u8 := 0x89
  const DUP11: u8 := 0x8a
  const DUP12: u8 := 0x8b
  const DUP13: u8 := 0x8c
  const DUP14: u8 := 0x8d
  const DUP15: u8 := 0x8e
  const DUP16: u8 := 0x8f
  // 90s: Exchange Operations
  const SWAP1: u8 := 0x90
  const SWAP2: u8 := 0x91
  const SWAP3: u8 := 0x92
  const SWAP4: u8 := 0x93
  const SWAP5: u8 := 0x94
  const SWAP6: u8 := 0x95
  const SWAP7: u8 := 0x96
  const SWAP8: u8 := 0x97
  const SWAP9: u8 := 0x98
  const SWAP10: u8 := 0x99
  const SWAP11: u8 := 0x9a
  const SWAP12: u8 := 0x9b
  const SWAP13: u8 := 0x9c
  const SWAP14: u8 := 0x9d
  const SWAP15: u8 := 0x9e
  const SWAP16: u8 := 0x9f
  // a0s: Logging Operations
  const LOG0: u8 := 0xa0
  const LOG1: u8 := 0xa1
  const LOG2: u8 := 0xa2
  const LOG3: u8 := 0xa3
  const LOG4: u8 := 0xa4
  // e0s
  const EOF: u8 := 0xef
  // f0s: System operations
  const CREATE: u8       := 0xf0
  const CALL: u8         := 0xf1
  const CALLCODE: u8     := 0xf2
  const RETURN: u8       := 0xf3
  const DELEGATECALL: u8 := 0xf4
  const CREATE2: u8      := 0xf5
  const STATICCALL: u8   := 0xfa
  const REVERT: u8       := 0xfd
  const INVALID: u8      := 0xfe
  const SELFDESTRUCT: u8 := 0xff

}
