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

include "./../utils/int.dfy"
include "./../utils/EVMOpcodes.dfy"

/**
  * Provide tooltips for EM instructions.
  */
module EVMToolTips {

  import opened Int
  import opened EVMOpcodes
  import opened EVMConstants

  /** The Dafny-EVM module that defines the semamtics of bytecode. */
  const bytecodeRefLine := "https://github.com/Consensys/evm-dafny/blob/60bce44ee75978a4c97b9eab8e03424c9c233bbd/src/dafny/bytecode.dfy#L"

  /**  The Dafny-EVM module that defines the gas cost. */
  const gasRefLine := "https://github.com/Consensys/evm-dafny/blob/60bce44ee75978a4c97b9eab8e03424c9c233bbd/src/dafny/evm.dfy#L103"

  /**
    * A tootlip (summary of effect) and the line in bytecode.dfy where the 
    * semantics is defined.
    */
  function ToolTip(op: u8): (string, nat)
  {
    match op
    case STOP       => ("Halts the machine without return output data", 32)
    case ADD        => ("Unsigned integer addition modulo TWO_256", 40)
    case MUL        => ("Unsigned integer multiplication modulo TWO_256", 61)
    case SUB        => ("Unsigned integer subtraction modulo TWO_256", 81)
    case DIV        => ("Unsigned integer division modulo TWO_256. Div by 0 yields 0", 154)
    case SDIV       => ("Signed integer division modulo TWO_256. Div by 0 yields 0", 173)
    case MOD        => ("Unsigned modulo remainder", 195)
    case SMOD       => ("Signed modulo remainder", 211)
    case ADDMOD     => ("Unsigned integer addition modulo", 230)
    case MULMOD     => ("Unsigned integer multiplication modulo", 250)
    case EXP        => ("Exponential", 272)
    case SIGNEXTEND => ("Extend length of two's complement signed integer", 291)
    // 0x10s: Comparison & Bitwise Logic
    case LT     => ("Unsigned Less than", 314)
    case GT     => ("Unsigned Greater than",336 )
    case SLT    => ("Signed less than",  358)
    case SGT    => ("Signed greater than", 380)
    case EQ     => ("equal", 402)
    case ISZERO => ("Is equal to zero", 424)

    case AND    => ("Bitwise AND", 445)
    case OR     => ("Bitwise OR", 464)
    case XOR    => ("Bitwise XOR", 484)
    case NOT    => ("Bitwise NOT", 504)
    case BYTE   => ("Extract a byte from a word.", 522)
    case SHL    => ("Left shift", 541)
    case SHR    => ("Right shift", 560)
    case SAR    => ("Arithmetic (signed) right shift operation", 579)
    // 0x20s
    case KECCAK256 => ("Keccak 256 hash", 598)
    // 0x30s: Environment Information
    case ADDRESS        => ("Address of current executing account", 640)
    case BALANCE        => ("Balance of a given account", 655)
    case ORIGIN         => ("Originator's address", 676)
    case CALLER         => ("Caller address", 692)
    case CALLVALUE      => ("Value deposited by function call", 707)
    case CALLDATALOAD   => ("Input data for this call", 723)
    case CALLDATASIZE   => ("Size of the input data", 742)
    case CALLDATACOPY   => ("Copy input data to memory", 759)
    case CODESIZE       => ("Size of the code of this contract", 783)
    case CODECOPY       => ("Copy the executing code to memory", 799)
    case GASPRICE       => ("Gas price in current block", 824)
    case EXTCODESIZE    => ("Size of the calling account's code", 839)
    case EXTCODECOPY    => ("Copy account's code to memory", 866)
    case RETURNDATASIZE => ("Size of return data from previous call", 920)
    case RETURNDATACOPY => ("Copy return data from previous call to memory", 937)
    case EXTCODEHASH    => ("Hash of account's code", 895)
    // 0x40s: Block Information
    case BLOCKHASH   => ("Hash of current block", 626)
    case COINBASE    => ("Current block's beneficiay address", 970)
    case TIMESTAMP   => ("Current block's timestamp", 985)
    case NUMBER      => ("Current block's number", 1000)
    case DIFFICULTY  => ("Current block's difficulty", 1015)
    case GASLIMIT    => ("Current block's gas limit", 1030)
    case CHAINID     => ("Chain ID", 1045)
    case SELFBALANCE => ("Balance of currently executing account", 1060)
    case BASEFEE     => ("Base fee for the currently executing block", 1080)
    // // 0x50s: Stack, Memory, Storage and Flow
    case POP      => ("Pop top of stack", 1097)
    case MLOAD    => ("Read a word from memory", 1133)
    case MSTORE   => ("Store a word to memory", 1165)
    case MSTORE8  => ("Store a byte to memory", 1195)
    case SLOAD    => ("Read a word from storage",1214 )
    case SSTORE   => ("Store a word to storage", 1233)
    case JUMP     => ("Uncoditional Jump", 1255)
    case JUMPI    => ("Conditional Jump", 1277)
    case RJUMP     => ("Static relative jump using a given offset", 1343 )
    case RJUMPI    => ("Conditional Static relative jump using a given offset", 1363)
    case RJUMPV    => ("Relative jump via a jump table of one or more relative offsets", 1392)
    case PC       => ("Value of program counter", 1302)
    case MSIZE    => ("Size of allocated memory",1113 )
    case GAS      => ("Amount of available gas", 1318)
    case JUMPDEST => ("A valid destination for a jump", 1334)
    case PUSH0    => ("Push 0 on stack", 1428)
    // // 0x60s & 0x70s: Push operations
    case PUSH1 => ("Push 1 byte", 1479)
    case PUSH2 => ("Push 2 bytes", 1486)
    case PUSH3 => ("Push 3 bytes", 1493)
    case PUSH4 => ("Push 4 bytes", 1500)
    case PUSH5 => ("Push 5 bytes", 1507)
    case PUSH6 => ("Push 6 bytes", 1514)
    case PUSH7 => ("Push 7 bytes", 1521)
    case PUSH8 => ("Push 8 bytes", 1528)
    case PUSH9 => ("Push 9 bytes", 1535 )
    case PUSH10 => ("Push 10 bytes", 1535)
    case PUSH11 => ("Push 11 bytes", 1535)
    case PUSH12 => ("Push 12 bytes", 1535)
    case PUSH13 => ("Push 13 bytes", 1535)
    case PUSH14 => ("Push 14 bytes", 1535)
    case PUSH15 => ("Push 15 bytes", 1535)
    case PUSH16 => ("Push 16 bytes", 1535)
    case PUSH17 => ("Push 17 bytes", 1535)
    case PUSH18 => ("Push 18 bytes", 1535)
    case PUSH19 => ("Push 19 bytes", 1535)
    case PUSH20 => ("Push 20 bytes", 1535)
    case PUSH21 => ("Push 21 bytes", 1535)
    case PUSH22 => ("Push 22 bytes", 1535)
    case PUSH23 => ("Push 23 bytes", 1535)
    case PUSH24 => ("Push 24 bytes", 1535)
    case PUSH25 => ("Push 25 bytes", 1535)
    case PUSH26 => ("Push 26 bytes", 1535)
    case PUSH27 => ("Push 27 bytes", 1535)
    case PUSH28 => ("Push 28 bytes", 1535)
    case PUSH29 => ("Push 29 bytes", 1535)
    case PUSH30 => ("Push 30 bytes", 1535)
    case PUSH31 => ("Push 31 bytes", 1535)
    case PUSH32 => ("Push 32 bytes", 1535)
    // // 0x80s: Duplicate operations
    case DUP1 => ("Duplicate 1st element on top of the stack", 1568)
    case DUP2 => ("Duplicate 2nd element on top of the stack", 1568)
    case DUP3 => ("Duplicate 3rd element on top of the stack", 1568)
    case DUP4 => ("Duplicate 4-th element on top of the stack", 1568)
    case DUP5 => ("Duplicate 5-th element on top of the stack", 1568)
    case DUP6 => ("Duplicate 6-th element on top of the stack", 1568)
    case DUP7 => ("Duplicate 7-th element on top of the stack", 1568)
    case DUP8 => ("Duplicate 8-th element on top of the stack", 1568)
    case DUP9 => ("Duplicate 9-th element on top of the stack", 1568)
    case DUP10 => ("Duplicate 10-th element on top of the stack", 1568)
    case DUP11 => ("Duplicate 11-th element on top of the stack", 1568)
    case DUP12 => ("Duplicate 12-th element on top of the stack", 1568)
    case DUP13 => ("Duplicate 13-th element on top of the stack", 1568)
    case DUP14 => ("Duplicate 14-th element on top of the stack", 1568)
    case DUP15 => ("Duplicate 15-th element on top of the stack", 1568)
    case DUP16 => ("Duplicate 16-th element on top of the stack", 1568)
    // // 0x90s: Exchange operations
    case SWAP1 => ("Swap top and 2nd element of the stack", 1577)
    case SWAP2 => ("Swap top and 3rd element of the stack", 1577)
    case SWAP3 => ("Swap top and 4-th element of the stack", 1577)
    case SWAP4 => ("Swap top and 5-th element of the stack", 1577)
    case SWAP5 => ("Swap top and 6-th element of the stack", 1577)
    case SWAP6 => ("Swap top and 7-th element of the stack", 1577)
    case SWAP7 => ("Swap top and 8-th element of the stack", 1577)
    case SWAP8 => ("Swap top and 9-th element of the stack", 1577)
    case SWAP9 => ("Swap top and 10-th element of the stack", 1577)
    case SWAP10 => ("Swap top and 11-th element of the stack", 1577)
    case SWAP11 => ("Swap top and 12-th element of the stack", 1577)
    case SWAP12 => ("Swap top and 13-th element of the stack", 1577)
    case SWAP13 => ("Swap top and 14-th element of the stack", 1577)
    case SWAP14 => ("Swap top and 15-th element of the stack", 1577)
    case SWAP15 => ("Swap top and 16-th element of the stack", 1577)
    case SWAP16 => ("Swap top and 17-th element of the stack", 1577)
    // // 0xA0s: Log operations
    case LOG0 => ("Append log with 0 topics", 1600)
    case LOG1 => ("Append log with 1 topics", 1600)
    case LOG2 => ("Append log with 2 topics", 1600)
    case LOG3 => ("Append log with 3 topics", 1600)
    case LOG4 => ("Append log with 4 topics", 1600)
    // // 0xf0
    case CREATE => ("Create a new account with associated code", 1629)
    // //  @todo: verify call effect on stack
    case CALL => ("Message-call into an account", 1674)
    case CALLCODE => ("Message-call into this account with another account's code", 1711)
    case RETURN => ("Halt execution and return data", 1742)
    case DELEGATECALL => ("Message-call into this account with an alternative account's code", 1764)
    case CREATE2 => ("Create a new account with associated code", 1799)
    case STATICCALL => ("Static Message-call into an account", 1844)
    case REVERT => ("Revert execution and return data", 1874)
    case SELFDESTRUCT => ("Delete this account", 1896)
    case INVALID => ("Equivalent to STOP", 32)
    case _ => ("N/A", 0)
  }

  /** Some constants - From the Dafny-EVM repo. */
  const G_ZERO: nat := 0
  const G_JUMPDEST: nat := 1
  const G_BASE: nat := 2
  const G_VERYLOW: nat := 3
  const G_LOW: nat := 5
  const G_MID: nat := 8
  const G_HIGH: nat := 10
  // Cost of a warm account or storage access
  const G_WARMACCESS: nat := 100
  // Cost of a cold account access.
  const G_COLDACCOUNTACCESS: nat := 2600
  // Cost of cold storage access
  const G_COLDSLOAD: nat := 2100
  const G_SSET: nat := 20000
  const G_SRESET: nat := 2900
  const R_SCLEAR: nat := 15000
  const R_SELFDESTRUCT: nat := 24000
  const G_SELFDESTRUCT: nat := 5000
  const G_CREATE: nat := 32000
  const G_CODEDEPOSIT: nat := 200
  const G_CALLVALUE: nat := 9000
  const G_CALLSTIPEND: nat := 2300
  const G_NEWACCOUNT: nat := 25000
  const G_EXP: nat := 10
  const G_EXPBYTE: nat := 50
  const G_MEMORY: nat := 3
  const G_TXCREATE: nat := 32000
  const G_TXDATAZERO: nat := 4
  const G_TXDATANONZERO: nat := 16
  const G_TRANSACTION: nat := 21000
  const G_LOG: nat := 375
  const G_LOGDATA: nat := 8
  const G_LOGTOPIC: nat := 375
  const G_KECCAK256: nat := 30
  const G_KECCAK256WORD: nat := 6
  const G_COPY: nat := 3
  const G_BLOCKHASH: nat := 20

  /**The gas cost for constant gas-cost instructions.  */
  function Gas(op: u8): string
  {
    match op
    case STOP => NatToString(G_ZERO)
    case ADD => NatToString(G_VERYLOW)
    case MUL => NatToString(G_LOW)
    case SUB => NatToString(G_VERYLOW)
    case DIV => NatToString(G_LOW)
    case SDIV => NatToString(G_LOW)
    case MOD => NatToString(G_LOW)
    case SMOD => NatToString(G_LOW)
    case ADDMOD => NatToString(G_MID)
    case MULMOD => NatToString(G_MID)
    case EXP => "Depends on memory expansion"
    case SIGNEXTEND => NatToString(G_LOW)
    // 0x10s: Comparison & Bitwise Logic
    case LT => NatToString(G_VERYLOW)
    case GT => NatToString(G_VERYLOW)
    case SLT => NatToString(G_VERYLOW)
    case SGT => NatToString(G_VERYLOW)
    case EQ => NatToString(G_VERYLOW)
    case ISZERO => NatToString(G_VERYLOW)
    case AND => NatToString(G_VERYLOW)
    case OR => NatToString(G_VERYLOW)
    case XOR => NatToString(G_VERYLOW)
    case NOT => NatToString(G_VERYLOW)
    case BYTE => NatToString(G_VERYLOW)
    case SHL => NatToString(G_VERYLOW)
    case SHR => NatToString(G_VERYLOW)
    case SAR => NatToString(G_VERYLOW)
    // 0x20s
    case KECCAK256 => "Depends on memory expansion"
    // 0x30s: Environment Information
    case ADDRESS => NatToString(G_BASE)
    // case BALANCE => NatToString(CostExtAccount(s))
    case ORIGIN => NatToString(G_BASE)
    case CALLER => NatToString(G_BASE)
    case CALLVALUE => NatToString(G_BASE)
    case CALLDATALOAD => NatToString(G_VERYLOW)
    case CALLDATASIZE => NatToString(G_BASE)
    case CALLDATACOPY => "Depends on memory expansion"
    case CODESIZE => NatToString(G_BASE)
    case CODECOPY => "Depends on memory expansion"
    case GASPRICE => NatToString(G_BASE)
    case EXTCODESIZE => "Depends on memory expansion"
    case EXTCODECOPY => "Depends on memory expansion"
    case RETURNDATASIZE => NatToString(G_BASE)
    case RETURNDATACOPY => "Depends on memory expansion"
    case EXTCODEHASH => "Depends on memory expansion"
    // 0x40s: Block Information
    case BLOCKHASH => NatToString(G_BLOCKHASH)
    case COINBASE => NatToString(G_BASE)
    case TIMESTAMP => NatToString(G_BASE)
    case NUMBER => NatToString(G_BASE)
    case DIFFICULTY => NatToString(G_BASE)
    case GASLIMIT => NatToString(G_BASE)
    case CHAINID => NatToString(G_BASE)
    case SELFBALANCE => NatToString(G_LOW)
    case BASEFEE => NatToString(G_BASE)
    // 0x50s: Stack, Memory, Storage and Flow
    case POP => NatToString(G_BASE)
    case MLOAD => "Depends on memory expansion"
    case MSTORE => "Depends on memory expansion"
    case MSTORE8 => "Depends on memory expansion"
    case SLOAD => "Depends on memory expansion"
    case SSTORE => "Depends on memory expansion"
    case JUMP => NatToString(G_MID)
    case JUMPI => NatToString(G_HIGH) // for now
    case PC => NatToString(G_BASE)
    case MSIZE => NatToString(G_BASE)
    case GAS => NatToString(G_BASE)
    case JUMPDEST => NatToString(G_JUMPDEST)
    // 0x60s & 0x70s: Push operations
    case PUSH0 => NatToString(G_VERYLOW)
    case PUSH1 => NatToString(G_VERYLOW)
    case PUSH2 => NatToString(G_VERYLOW)
    case PUSH3 => NatToString(G_VERYLOW)
    case PUSH4 => NatToString(G_VERYLOW)
    case PUSH5 => NatToString(G_VERYLOW)
    case PUSH6 => NatToString(G_VERYLOW)
    case PUSH7 => NatToString(G_VERYLOW)
    case PUSH8 => NatToString(G_VERYLOW)
    case PUSH9 => NatToString(G_VERYLOW)
    case PUSH10 => NatToString(G_VERYLOW)
    case PUSH11 => NatToString(G_VERYLOW)
    case PUSH12 => NatToString(G_VERYLOW)
    case PUSH13 => NatToString(G_VERYLOW)
    case PUSH14 => NatToString(G_VERYLOW)
    case PUSH15 => NatToString(G_VERYLOW)
    case PUSH16 => NatToString(G_VERYLOW)
    case PUSH17 => NatToString(G_VERYLOW)
    case PUSH18 => NatToString(G_VERYLOW)
    case PUSH19 => NatToString(G_VERYLOW)
    case PUSH20 => NatToString(G_VERYLOW)
    case PUSH21 => NatToString(G_VERYLOW)
    case PUSH22 => NatToString(G_VERYLOW)
    case PUSH23 => NatToString(G_VERYLOW)
    case PUSH24 => NatToString(G_VERYLOW)
    case PUSH25 => NatToString(G_VERYLOW)
    case PUSH26 => NatToString(G_VERYLOW)
    case PUSH27 => NatToString(G_VERYLOW)
    case PUSH28 => NatToString(G_VERYLOW)
    case PUSH29 => NatToString(G_VERYLOW)
    case PUSH30 => NatToString(G_VERYLOW)
    case PUSH31 => NatToString(G_VERYLOW)
    case PUSH32 => NatToString(G_VERYLOW)
    // 0x80s: Duplicate operations
    case DUP1 => NatToString(G_VERYLOW)
    case DUP2 => NatToString(G_VERYLOW)
    case DUP3 => NatToString(G_VERYLOW)
    case DUP4 => NatToString(G_VERYLOW)
    case DUP5 => NatToString(G_VERYLOW)
    case DUP6 => NatToString(G_VERYLOW)
    case DUP7 => NatToString(G_VERYLOW)
    case DUP8 => NatToString(G_VERYLOW)
    case DUP9 => NatToString(G_VERYLOW)
    case DUP10 => NatToString(G_VERYLOW)
    case DUP11 => NatToString(G_VERYLOW)
    case DUP12 => NatToString(G_VERYLOW)
    case DUP13 => NatToString(G_VERYLOW)
    case DUP14 => NatToString(G_VERYLOW)
    case DUP15 => NatToString(G_VERYLOW)
    case DUP16 => NatToString(G_VERYLOW)
    // 0x90s: Exchange operations
    case SWAP1 => NatToString(G_VERYLOW)
    case SWAP2 => NatToString(G_VERYLOW)
    case SWAP3 => NatToString(G_VERYLOW)
    case SWAP4 => NatToString(G_VERYLOW)
    case SWAP5 => NatToString(G_VERYLOW)
    case SWAP6 => NatToString(G_VERYLOW)
    case SWAP7 => NatToString(G_VERYLOW)
    case SWAP8 => NatToString(G_VERYLOW)
    case SWAP9 => NatToString(G_VERYLOW)
    case SWAP10 => NatToString(G_VERYLOW)
    case SWAP11 => NatToString(G_VERYLOW)
    case SWAP12 => NatToString(G_VERYLOW)
    case SWAP13 => NatToString(G_VERYLOW)
    case SWAP14 => NatToString(G_VERYLOW)
    case SWAP15 => NatToString(G_VERYLOW)
    case SWAP16 => NatToString(G_VERYLOW)
    // 0xA0s: Log operations
    case LOG0 => "Depends on memory expansion"
    case LOG1 => "Depends on memory expansion"
    case LOG2 => "Depends on memory expansion"
    case LOG3 => "Depends on memory expansion"
    case LOG4 => "Depends on memory expansion"
    // 0xf0
    case CREATE => "Depends on memory expansion"
    case CALL => "Depends on memory expansion"
    case CALLCODE => "Depends on memory expansion"
    case RETURN => "Depends on memory expansion"
    case DELEGATECALL => "Depends on memory expansion"
    case CREATE2 => "Depends on memory expansion"
    case STATICCALL => "Depends on memory expansion"
    case REVERT => "Depends on memory expansion"
    case SELFDESTRUCT => "Depends on memory expansion"
    case INVALID => NatToString(G_VERYLOW)
    case _ => "Unknown opcode"

  }

}