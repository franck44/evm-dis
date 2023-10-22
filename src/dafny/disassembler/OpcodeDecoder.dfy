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

include "./../utils/int.dfy"
include "./../utils/EVMOpcodes.dfy"

/**
  * Provides EVM opcodes decoding into readable format.
  */
module OpcodeDecoder {

  import opened Int
  import opened EVMOpcodes

  /**
    *   Decode an opcode.
    *   @param op   The hex/u8 value to decode.
    *   @returns    The readable opcode that corresponds to `op`.
    *   @note       If opcode is not in the set of EVM opcodes, returns `INVALID`.
    */
  function Decode(op: u8): Opcode {
    match op
    case STOP => SysOp("STOP", STOP)
    case ADD => ArithOp("ADD", ADD)
    case MUL => ArithOp("MUL", MUL)
    case SUB => ArithOp("SUB", SUB)
    case DIV => ArithOp("DIV", DIV)
    case SDIV => ArithOp("SDIV", SDIV)
    case MOD => ArithOp("MOD", MOD)
    case SMOD => ArithOp("SMOD", SMOD)
    case ADDMOD => ArithOp("ADDMOD", ADDMOD)
    case MULMOD => ArithOp("MULMOD", MULMOD)
    case EXP => ArithOp("EXP", EXP)
    case SIGNEXTEND => ArithOp("SIGNEXTEND", SIGNEXTEND)
    // 0x10s: Comparison & Bitwise Logic
    case LT => CompOp("LT", LT)
    case GT => CompOp("GT", GT)
    case SLT => CompOp("SLT", SLT)
    case SGT => CompOp("SGT", SGT)
    case EQ => CompOp("EQ", EQ)
    case ISZERO => CompOp("ISZERO", ISZERO)
    case AND => BitwiseOp("AND", AND)
    case OR => BitwiseOp("OR", OR)
    case XOR => BitwiseOp("XOR", XOR)
    case NOT => BitwiseOp("NOT", NOT)
    case BYTE => BitwiseOp("BYTE", BYTE)
    case SHL => BitwiseOp("SHL", SHL)
    case SHR => BitwiseOp("SHR", SHR)
    case SAR => BitwiseOp("SAR", SAR)
    // 0x20s
    case KECCAK256 => KeccakOp("KECCAK256", KECCAK256)
    // 0x30s: Environment Information
    case ADDRESS => EnvOp("ADDRESS", ADDRESS)
    case BALANCE => EnvOp("BALANCE", BALANCE)
    case ORIGIN => EnvOp("ORIGIN", ORIGIN)
    case CALLER => EnvOp("CALLER", CALLER)
    case CALLVALUE => EnvOp("CALLVALUE", CALLVALUE)
    case CALLDATALOAD => EnvOp("CALLDATALOAD", CALLDATALOAD)
    case CALLDATASIZE => EnvOp("CALLDATASIZE", CALLDATASIZE)
    case CALLDATACOPY => EnvOp("CALLDATACOPY", CALLDATACOPY)
    case CODESIZE => EnvOp("CODESIZE", CODESIZE)
    case CODECOPY => EnvOp("CODECOPY", CODECOPY)
    case GASPRICE => EnvOp("GASPRICE", GASPRICE)
    case EXTCODESIZE => EnvOp("EXTCODESIZE", EXTCODESIZE)
    case EXTCODECOPY => EnvOp("EXTCODECOPY", EXTCODECOPY)
    case RETURNDATASIZE => EnvOp("RETURNDATASIZE", RETURNDATASIZE)
    case RETURNDATACOPY => EnvOp("RETURNDATACOPY", RETURNDATACOPY)
    case EXTCODEHASH => EnvOp("EXTCODEHASH", EXTCODEHASH)
    // 0x40s: Block Information
    case BLOCKHASH => EnvOp("BLOCKHASH", BLOCKHASH)
    case COINBASE => EnvOp("COINBASE", COINBASE)
    case TIMESTAMP => EnvOp("TIMESTAMP", TIMESTAMP)
    case NUMBER => EnvOp("NUMBER", NUMBER)
    case DIFFICULTY => EnvOp("DIFFICULTY", DIFFICULTY)
    case GASLIMIT => EnvOp("GASLIMIT", GASLIMIT)
    case CHAINID => EnvOp("CHAINID", CHAINID)
    case SELFBALANCE => EnvOp("SELFBALANCE", SELFBALANCE)
    case BASEFEE => EnvOp("BASEFEE", BASEFEE)
    // 0x50s: Stack, Memory, Storage and Flow
    case POP => StackOp("POP", POP)
    case MLOAD => MemOp("MLOAD", MLOAD)
    case MSTORE => MemOp("MSTORE", MSTORE)
    case MSTORE8 => MemOp("MSTORE8", MSTORE8)
    case SLOAD => StorageOp("SLOAD", SLOAD)
    case SSTORE => StorageOp("SSTORE", SSTORE)
    case JUMP => JumpOp("JUMP", JUMP)
    case JUMPI => JumpOp("JUMPI", JUMPI)
    case PC => RunOp("PC", PC)
    case MSIZE => RunOp("MSIZE", MSIZE)
    case GAS => RunOp("GAS", GAS)
    case JUMPDEST => JumpOp("JUMPDEST", JUMPDEST)
    case PUSH0 => StackOp("PUSH0", PUSH0)
    // 0x60s & 0x70s: Push operations
    case PUSH1 => StackOp("PUSH1", PUSH1)
    case PUSH2 => StackOp("PUSH2", PUSH2)
    case PUSH3 => StackOp("PUSH3", PUSH3)
    case PUSH4 => StackOp("PUSH4", PUSH4)
    case PUSH5 => StackOp("PUSH5", PUSH5)
    case PUSH6 => StackOp("PUSH6", PUSH6)
    case PUSH7 => StackOp("PUSH7", PUSH7)
    case PUSH8 => StackOp("PUSH8", PUSH8)
    case PUSH9 => StackOp("PUSH9", PUSH9)
    case PUSH10 => StackOp("PUSH10", PUSH10)
    case PUSH11 => StackOp("PUSH11", PUSH11)
    case PUSH12 => StackOp("PUSH12", PUSH12)
    case PUSH13 => StackOp("PUSH13", PUSH13)
    case PUSH14 => StackOp("PUSH14", PUSH14)
    case PUSH15 => StackOp("PUSH15", PUSH15)
    case PUSH16 => StackOp("PUSH16", PUSH16)
    case PUSH17 => StackOp("PUSH17", PUSH17)
    case PUSH18 => StackOp("PUSH18", PUSH18)
    case PUSH19 => StackOp("PUSH19", PUSH19)
    case PUSH20 => StackOp("PUSH20", PUSH20)
    case PUSH21 => StackOp("PUSH21", PUSH21)
    case PUSH22 => StackOp("PUSH22", PUSH22)
    case PUSH23 => StackOp("PUSH23", PUSH23)
    case PUSH24 => StackOp("PUSH24", PUSH24)
    case PUSH25 => StackOp("PUSH25", PUSH25)
    case PUSH26 => StackOp("PUSH26", PUSH26)
    case PUSH27 => StackOp("PUSH27", PUSH27)
    case PUSH28 => StackOp("PUSH28", PUSH28)
    case PUSH29 => StackOp("PUSH29", PUSH29)
    case PUSH30 => StackOp("PUSH30", PUSH30)
    case PUSH31 => StackOp("PUSH31", PUSH31)
    case PUSH32 => StackOp("PUSH32", PUSH32)
    // 0x80s: Duplicate operations
    case DUP1 => StackOp("DUP1", DUP1)
    case DUP2 => StackOp("DUP2", DUP2)
    case DUP3 => StackOp("DUP3", DUP3)
    case DUP4 => StackOp("DUP4", DUP4)
    case DUP5 => StackOp("DUP5", DUP5)
    case DUP6 => StackOp("DUP6", DUP6)
    case DUP7 => StackOp("DUP7", DUP7)
    case DUP8 => StackOp("DUP8", DUP8)
    case DUP9 => StackOp("DUP9", DUP9)
    case DUP10 => StackOp("DUP10", DUP10)
    case DUP11 => StackOp("DUP11", DUP11)
    case DUP12 => StackOp("DUP12", DUP12)
    case DUP13 => StackOp("DUP13", DUP13)
    case DUP14 => StackOp("DUP14", DUP14)
    case DUP15 => StackOp("DUP15", DUP15)
    case DUP16 => StackOp("DUP16", DUP16)
    // 0x90s: Exchange operations
    case SWAP1 => StackOp("SWAP1", SWAP1)
    case SWAP2 => StackOp("SWAP2", SWAP2)
    case SWAP3 => StackOp("SWAP3", SWAP3)
    case SWAP4 => StackOp("SWAP4", SWAP4)
    case SWAP5 => StackOp("SWAP5", SWAP5)
    case SWAP6 => StackOp("SWAP6", SWAP6)
    case SWAP7 => StackOp("SWAP7", SWAP7)
    case SWAP8 => StackOp("SWAP8", SWAP8)
    case SWAP9 => StackOp("SWAP9", SWAP9)
    case SWAP10 => StackOp("SWAP10", SWAP10)
    case SWAP11 => StackOp("SWAP11", SWAP11)
    case SWAP12 => StackOp("SWAP12", SWAP12)
    case SWAP13 => StackOp("SWAP13", SWAP13)
    case SWAP14 => StackOp("SWAP14", SWAP14)
    case SWAP15 => StackOp("SWAP15", SWAP15)
    case SWAP16 => StackOp("SWAP16", SWAP16)
    // 0xA0s: Log operations
    case LOG0 => LogOp("LOG0", LOG0)
    case LOG1 => LogOp("LOG1", LOG1)
    case LOG2 => LogOp("LOG2", LOG2)
    case LOG3 => LogOp("LOG3", LOG3)
    case LOG4 => LogOp("LOG4", LOG4)
    // 0xf0
    case CREATE => SysOp("CREATE", CREATE)
    case CALL => SysOp("CALL", CALL)
    case CALLCODE => SysOp("CALLCODE", CALLCODE)
    case RETURN => SysOp("RETURN", RETURN)
    case DELEGATECALL => SysOp("DELEGATECALL", DELEGATECALL)
    case CREATE2 => SysOp("CREATE2", CREATE2)
    case STATICCALL => SysOp("STATICCALL", STATICCALL)
    case REVERT => SysOp("REVERT", REVERT)
    case SELFDESTRUCT => SysOp("SELFDESTRUCT", SELFDESTRUCT)
    case _ => SysOp("INVALID", INVALID)
  }

}