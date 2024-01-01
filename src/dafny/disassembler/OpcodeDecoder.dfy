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
  import opened EVMConstants

  /** 
    *   Decode an opcode.
    *   @param op   The hex/u8 value to decode.
    *   @returns    The readable opcode that corresponds to `op`.
    *   @note       If opcode is not in the set of EVM opcodes, returns `INVALID`.
    *   @note       Don't make it {:opaque} as othewise the instruction that corresponds 
    *               to opcode is not knowm and cannot proved to be Valid.
    */
  function Decode(op: u8): Opcode
    ensures Decode(op).IsValid()
  {
    // parameters are: name, value of opcode, minCapacity, minOperands, pushes, pops
    match op
    case STOP       => SysOp("STOP", STOP, 0, 0, 0, 0)
    case ADD        => ArithOp("ADD", ADD)
    case MUL        => ArithOp("MUL", MUL)
    case SUB        => ArithOp("SUB", SUB)
    case DIV        => ArithOp("DIV", DIV)
    case SDIV       => ArithOp("SDIV", SDIV)
    case MOD        => ArithOp("MOD", MOD)
    case SMOD       => ArithOp("SMOD", SMOD)
    case ADDMOD     => ArithOp("ADDMOD", ADDMOD)
    case MULMOD     => ArithOp("MULMOD", MULMOD)
    case EXP        => ArithOp("EXP", EXP)
    case SIGNEXTEND => ArithOp("SIGNEXTEND", SIGNEXTEND)
    // 0x10s: Comparison & Bitwise Logic
    case LT     => CompOp("LT", LT)
    case GT     => CompOp("GT", GT)
    case SLT    => CompOp("SLT", SLT)
    case SGT    => CompOp("SGT", SGT)
    case EQ     => CompOp("EQ", EQ)
    case ISZERO => CompOp("ISZERO", ISZERO, 0, 1, 1, 1)

    case AND    => BitwiseOp("AND", AND, 0, 2, 1, 2)
    case OR     => BitwiseOp("OR", OR, 0, 2, 1, 2)
    case XOR    => BitwiseOp("XOR", XOR, 0, 2, 1, 2)
    case NOT    => BitwiseOp("NOT", NOT, 0, 1, 1, 1)
    case BYTE   => BitwiseOp("BYTE", BYTE, 0, 2, 1, 2)
    case SHL    => BitwiseOp("SHL", SHL, 0, 2, 1, 2)
    case SHR    => BitwiseOp("SHR", SHR, 0, 2, 1, 2)
    case SAR    => BitwiseOp("SAR", SAR, 0, 2, 1, 2)
    // 0x20s
    case KECCAK256 => KeccakOp("KECCAK256", KECCAK256, 0, 2, 1, 2)
    // 0x30s: Environment Information
    case ADDRESS        => EnvOp("ADDRESS", ADDRESS, 1, 0, 1, 0)
    case BALANCE        => EnvOp("BALANCE", BALANCE, 0, 1, 1, 1)
    case ORIGIN         => EnvOp("ORIGIN", ORIGIN, 1, 0, 1, 0)
    case CALLER         => EnvOp("CALLER", CALLER, 1, 0, 1, 0)
    case CALLVALUE      => EnvOp("CALLVALUE", CALLVALUE, 1, 0, 1, 0)
    case CALLDATALOAD   => EnvOp("CALLDATALOAD", CALLDATALOAD, 0 , 1, 1, 1)
    case CALLDATASIZE   => EnvOp("CALLDATASIZE", CALLDATASIZE, 1, 0, 1, 0)
    case CALLDATACOPY   => EnvOp("CALLDATACOPY", CALLDATACOPY, 0, 3, 0, 3)
    case CODESIZE       => EnvOp("CODESIZE", CODESIZE, 1, 0, 1, 0)
    case CODECOPY       => EnvOp("CODECOPY", CODECOPY, 0, 3, 0, 3)
    case GASPRICE       => EnvOp("GASPRICE", GASPRICE, 1, 0, 1, 0)
    case EXTCODESIZE    => EnvOp("EXTCODESIZE", EXTCODESIZE, 0, 1, 1, 1)
    case EXTCODECOPY    => EnvOp("EXTCODECOPY", EXTCODECOPY, 0, 4, 0, 4)
    case RETURNDATASIZE => EnvOp("RETURNDATASIZE", RETURNDATASIZE, 1, 0, 1, 0)
    case RETURNDATACOPY => EnvOp("RETURNDATACOPY", RETURNDATACOPY, 0, 3, 0, 3)
    case EXTCODEHASH    => EnvOp("EXTCODEHASH", EXTCODEHASH, 0, 1, 1, 1)
    // 0x40s: Block Information
    case BLOCKHASH   => EnvOp("BLOCKHASH", BLOCKHASH, 0, 1, 1, 1)
    case COINBASE    => EnvOp("COINBASE", COINBASE, 1, 0, 1, 0)
    case TIMESTAMP   => EnvOp("TIMESTAMP", TIMESTAMP, 1, 0, 1, 0)
    case NUMBER      => EnvOp("NUMBER", NUMBER, 1, 0, 1, 0)
    case DIFFICULTY  => EnvOp("DIFFICULTY", DIFFICULTY, 1, 0, 1, 0)
    case GASLIMIT    => EnvOp("GASLIMIT", GASLIMIT, 1, 0, 1, 0)
    case CHAINID     => EnvOp("CHAINID", CHAINID, 1, 0, 1, 0)
    case SELFBALANCE => EnvOp("SELFBALANCE", SELFBALANCE, 1, 0, 1, 0)
    case BASEFEE     => EnvOp("BASEFEE", BASEFEE, 1, 0, 1, 0)
    // 0x50s: Stack, Memory, Storage and Flow
    case POP      => StackOp("POP", POP, 0, 1, 0, 1)
    case MLOAD    => MemOp("MLOAD", MLOAD, 0, 1, 1, 1)
    case MSTORE   => MemOp("MSTORE", MSTORE, 0, 2, 0, 2)
    case MSTORE8  => MemOp("MSTORE8", MSTORE8, 0, 2, 0, 2)
    case SLOAD    => StorageOp("SLOAD", SLOAD, 0, 1, 1, 1)
    case SSTORE   => StorageOp("SSTORE", SSTORE, 0, 2, 0, 2)
    case JUMP     => JumpOp("JUMP", JUMP, 0, 1, 0, 1)
    case JUMPI    => JumpOp("JUMPI", JUMPI, 0, 2, 0, 2)
    case RJUMP     => JumpOp("RJUMP", RJUMP, 0, 1, 0, 1)
    case RJUMPI    => JumpOp("RJUMPI", RJUMPI, 0, 2, 0, 2)
    case RJUMPV    => JumpOp("RJUMPV", RJUMPV, 0, 2, 0, 2)
    case PC       => RunOp("PC", PC, 1, 0, 1, 0)
    case MSIZE    => RunOp("MSIZE", MSIZE, 1, 0, 1, 0)
    case GAS      => RunOp("GAS", GAS, 1, 0, 1, 0)
    case JUMPDEST => JumpOp("JUMPDEST", JUMPDEST, 0, 0, 0, 0)
    case PUSH0    => StackOp("PUSH0", PUSH0, 1, 0, 1, 0)
    // 0x60s & 0x70s: Push operations
    case PUSH1 => StackOp("PUSH1", PUSH1, 1, 0, 1, 0)
    case PUSH2 => StackOp("PUSH2", PUSH2, 1, 0, 1, 0)
    case PUSH3 => StackOp("PUSH3", PUSH3, 1, 0, 1, 0)
    case PUSH4 => StackOp("PUSH4", PUSH4, 1, 0, 1, 0)
    case PUSH5 => StackOp("PUSH5", PUSH5, 1, 0, 1, 0)
    case PUSH6 => StackOp("PUSH6", PUSH6, 1, 0, 1, 0)
    case PUSH7 => StackOp("PUSH7", PUSH7, 1, 0, 1, 0)
    case PUSH8 => StackOp("PUSH8", PUSH8, 1, 0, 1, 0)
    case PUSH9 => StackOp("PUSH9", PUSH9, 1, 0, 1, 0)
    case PUSH10 => StackOp("PUSH10", PUSH10, 1, 0, 1, 0)
    case PUSH11 => StackOp("PUSH11", PUSH11, 1, 0, 1, 0)
    case PUSH12 => StackOp("PUSH12", PUSH12, 1, 0, 1, 0)
    case PUSH13 => StackOp("PUSH13", PUSH13, 1, 0, 1, 0)
    case PUSH14 => StackOp("PUSH14", PUSH14, 1, 0, 1, 0)
    case PUSH15 => StackOp("PUSH15", PUSH15, 1, 0, 1, 0)
    case PUSH16 => StackOp("PUSH16", PUSH16, 1, 0, 1, 0)
    case PUSH17 => StackOp("PUSH17", PUSH17, 1, 0, 1, 0)
    case PUSH18 => StackOp("PUSH18", PUSH18, 1, 0, 1, 0)
    case PUSH19 => StackOp("PUSH19", PUSH19, 1, 0, 1, 0)
    case PUSH20 => StackOp("PUSH20", PUSH20, 1, 0, 1, 0)
    case PUSH21 => StackOp("PUSH21", PUSH21, 1, 0, 1, 0)
    case PUSH22 => StackOp("PUSH22", PUSH22, 1, 0, 1, 0)
    case PUSH23 => StackOp("PUSH23", PUSH23, 1, 0, 1, 0)
    case PUSH24 => StackOp("PUSH24", PUSH24, 1, 0, 1, 0)
    case PUSH25 => StackOp("PUSH25", PUSH25, 1, 0, 1, 0)
    case PUSH26 => StackOp("PUSH26", PUSH26, 1, 0, 1, 0)
    case PUSH27 => StackOp("PUSH27", PUSH27, 1, 0, 1, 0)
    case PUSH28 => StackOp("PUSH28", PUSH28, 1, 0, 1, 0)
    case PUSH29 => StackOp("PUSH29", PUSH29, 1, 0, 1, 0)
    case PUSH30 => StackOp("PUSH30", PUSH30, 1, 0, 1, 0)
    case PUSH31 => StackOp("PUSH31", PUSH31, 1, 0, 1, 0)
    case PUSH32 => StackOp("PUSH32", PUSH32, 1, 0, 1, 0)
    // 0x80s: Duplicate operations
    case DUP1 => StackOp("DUP1", DUP1, minCapacity := 1, minOperands := 1, pushes := 1, pops := 0)
    case DUP2 => StackOp("DUP2", DUP2, minCapacity := 1, minOperands := 2, pushes := 1, pops := 0)
    case DUP3 => StackOp("DUP3", DUP3, minCapacity := 1, minOperands := 3, pushes := 1, pops := 0)
    case DUP4 => StackOp("DUP4", DUP4, minCapacity := 1, minOperands := 4, pushes := 1, pops := 0)
    case DUP5 => StackOp("DUP5", DUP5, minCapacity := 1, minOperands := 5, pushes := 1, pops := 0)
    case DUP6 => StackOp("DUP6", DUP6, minCapacity := 1, minOperands := 6, pushes := 1, pops := 0)
    case DUP7 => StackOp("DUP7", DUP7, minCapacity := 1, minOperands := 7, pushes := 1, pops := 0)
    case DUP8 => StackOp("DUP8", DUP8, minCapacity := 1, minOperands := 8, pushes := 1, pops := 0)
    case DUP9 => StackOp("DUP9", DUP9, minCapacity := 1, minOperands := 9, pushes := 1, pops := 0)
    case DUP10 => StackOp("DUP10", DUP10, minCapacity := 1, minOperands := 10, pushes := 1, pops := 0)
    case DUP11 => StackOp("DUP11", DUP11, minCapacity := 1, minOperands := 11, pushes := 1, pops := 0)
    case DUP12 => StackOp("DUP12", DUP12, minCapacity := 1, minOperands := 12, pushes := 1, pops := 0)
    case DUP13 => StackOp("DUP13", DUP13, minCapacity := 1, minOperands := 13, pushes := 1, pops := 0)
    case DUP14 => StackOp("DUP14", DUP14, minCapacity := 1, minOperands := 14, pushes := 1, pops := 0)
    case DUP15 => StackOp("DUP15", DUP15, minCapacity := 1, minOperands := 15, pushes := 1, pops := 0)
    case DUP16 => StackOp("DUP16", DUP16, minCapacity := 1, minOperands := 16, pushes := 1, pops := 0)
    // 0x90s: Exchange operations
    case SWAP1 => StackOp("SWAP1", SWAP1, minCapacity := 0, minOperands := 1 + 1)
    case SWAP2 => StackOp("SWAP2", SWAP2, minCapacity := 0, minOperands := 2 + 1)
    case SWAP3 => StackOp("SWAP3", SWAP3, minCapacity := 0, minOperands := 3 + 1)
    case SWAP4 => StackOp("SWAP4", SWAP4, minCapacity := 0, minOperands := 4 + 1)
    case SWAP5 => StackOp("SWAP5", SWAP5, minCapacity := 0, minOperands := 5 + 1)
    case SWAP6 => StackOp("SWAP6", SWAP6, minCapacity := 0, minOperands := 6 + 1)
    case SWAP7 => StackOp("SWAP7", SWAP7, minCapacity := 0, minOperands := 7 + 1)
    case SWAP8 => StackOp("SWAP8", SWAP8, minCapacity := 0, minOperands := 8 + 1)
    case SWAP9 => StackOp("SWAP9", SWAP9, minCapacity := 0, minOperands := 9 + 1)
    case SWAP10 => StackOp("SWAP10", SWAP10, minCapacity := 0, minOperands := 10 + 1)
    case SWAP11 => StackOp("SWAP11", SWAP11, minCapacity := 0, minOperands := 11 + 1)
    case SWAP12 => StackOp("SWAP12", SWAP12, minCapacity := 0, minOperands := 12 + 1)
    case SWAP13 => StackOp("SWAP13", SWAP13, minCapacity := 0, minOperands := 13 + 1)
    case SWAP14 => StackOp("SWAP14", SWAP14, minCapacity := 0, minOperands := 14 + 1)
    case SWAP15 => StackOp("SWAP15", SWAP15, minCapacity := 0, minOperands := 15 + 1)
    case SWAP16 => StackOp("SWAP16", SWAP16, minCapacity := 0, minOperands := 16 + 1)
    // 0xA0s: Log operations
    case LOG0 => LogOp("LOG0", LOG0, 0, 0 + 2, 0, 0 + 2)
    case LOG1 => LogOp("LOG1", LOG1, 0, 1 + 2, 0, 1 + 2)
    case LOG2 => LogOp("LOG2", LOG2, 0, 2 + 2, 0, 2 + 2)
    case LOG3 => LogOp("LOG3", LOG3, 0, 3 + 2, 0, 3 + 2)
    case LOG4 => LogOp("LOG4", LOG4, 0, 4 + 2, 0, 4 + 2)
    // 0xf0
    case CREATE => SysOp("CREATE", CREATE, 1, 3, 1, 3)
    //  @todo: verify call effect on stack
    case CALL => SysOp("CALL", CALL, 1, 7, 1, 7)
    case CALLCODE => SysOp("CALLCODE", CALLCODE, 1, 7, 1, 7)
    case RETURN => SysOp("RETURN", RETURN, 0, 2, 0, 0)
    case DELEGATECALL => SysOp("DELEGATECALL", DELEGATECALL, 1, 6, 1, 6)
    case CREATE2 => SysOp("CREATE2", CREATE2, 1, 4, 1, 4)
    case STATICCALL => SysOp("STATICCALL", STATICCALL,1, 6, 1, 6)
    case REVERT => SysOp("REVERT", REVERT, 0, 2, 0, 0)
    case SELFDESTRUCT => SysOp("SELFDESTRUCT", SELFDESTRUCT, 0, 1, 0, 1)
    case _ => SysOp("INVALID", INVALID, 0, 0, 0, 0)
  }

}