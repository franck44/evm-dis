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

include "../utils/Instructions.dfy"
include "../utils/OpcodesConstants.dfy"
include "../utils/EVMOpcodes.dfy"

/**
  *  Provides pretty printers\ for instruction.
  * @note   For some reasons unknown to me, including this function in Pretty.dfy
  *         results in redundant branch warning. There seems to be issues 
  *         with case K when k is a integer.
  */
module PrettyIns {

  import EVMOpcodes
  import opened Instructions
  import opened EVMConstants

  /**
    *   @param  src Name of the source state,
    *   @param  tgt Name of the new target state.
    */
  function PrintInstructionToDafny(i: Instruction, src: nat, tgt: nat): string
  {
    match i.op.opcode
    case STOP       => "var s" + DecToString(tgt) + " := Stop(s" + DecToString(src) + ");"
    case ADD         => "var s" + DecToString(tgt) + " := Add(s" + DecToString(src) + ");"
    case MUL        => "var s" + DecToString(tgt) + " := Mul(s" + DecToString(src) + ");"
    case SUB        => "var s" + DecToString(tgt) + " := Sub(s" + DecToString(src) + ");"
    case DIV        => "var s" + DecToString(tgt) + " := Div(s" + DecToString(src) + ");"
    case SDIV       => "var s" + DecToString(tgt) + " := SDiv(s" + DecToString(src) + ");"
    case MOD        => "var s" + DecToString(tgt) + " := Mod(s" + DecToString(src) + ");"
    case SMOD       => "var s" + DecToString(tgt) + " := SMod(s" + DecToString(src) + ");"
    case ADDMOD     => "var s" + DecToString(tgt) + " := AddMod(s" + DecToString(src) + ");"
    case MULMOD     => "var s" + DecToString(tgt) + " := MulMod(s" + DecToString(src) + ");"
    case EXP        => "var s" + DecToString(tgt) + " := Exp(s" + DecToString(src) + ");"
    case SIGNEXTEND => "var s" + DecToString(tgt) + " := SignExtended(s" + DecToString(src) + ");"
    // 0x10s: Comparison & Bitwise Logic
    case LT     => "var s" + DecToString(tgt) + " := Lt(s" + DecToString(src) + ");"
    case GT     => "var s" + DecToString(tgt) + " := Gt(s" + DecToString(src) + ");"
    case SLT    => "var s" + DecToString(tgt) + " := Slt(s" + DecToString(src) + ");"
    case SGT    => "var s" + DecToString(tgt) + " := Sgt(s" + DecToString(src) + ");"
    case EQ     => "var s" + DecToString(tgt) + " := Eq(s" + DecToString(src) + ");"
    case ISZERO => "var s" + DecToString(tgt) + " := IsZero(s" + DecToString(src) + ");"
    case AND    => "var s" + DecToString(tgt) + " := And(s" + DecToString(src) + ");"
    case OR     => "var s" + DecToString(tgt) + " := Or(s" + DecToString(src) + ");"
    case XOR    => "var s" + DecToString(tgt) + " := Xor(s" + DecToString(src) + ");"
    case NOT    => "var s" + DecToString(tgt) + " := Not(s" + DecToString(src) + ");"
    case BYTE   => "var s" + DecToString(tgt) + " := Byte(s" + DecToString(src) + ");"
    case SHL    => "var s" + DecToString(tgt) + " := Shl(s" + DecToString(src) + ");"
    case SHR    => "var s" + DecToString(tgt) + " := Shr(s" + DecToString(src) + ");"
    case SAR    => "var s" + DecToString(tgt) + " := Sar(s" + DecToString(src) + ");"
    // // 0x20s
    case KECCAK256 => "var s" + DecToString(tgt) + " := Keccak256(s" + DecToString(src) + ");"
    // // 0x30s: Environment Information
    case ADDRESS        =>  "var s" + DecToString(tgt) + " := Address(s" + DecToString(src) + ");"
    case BALANCE => "var s" + DecToString(tgt) + " := Balance(s" + DecToString(src) + ");"
    // case BALANCE        => EnvOp("BALANCE", BALANCE)
    // case ORIGIN         => EnvOp("ORIGIN", ORIGIN)
    case CALLER         =>  "var s" + DecToString(tgt) + " := Caller(s" + DecToString(src) + ");"
    case CALLVALUE      => "var s" + DecToString(tgt) + " := CallValue(s" + DecToString(src) + ");"
    case CALLDATALOAD   => "var s" + DecToString(tgt) + " := CallDataLoad(s" + DecToString(src) + ");"
    case CALLDATASIZE   => "var s" + DecToString(tgt) + " := CallDataSize(s" + DecToString(src) + ");"
    case CALLDATACOPY   =>  "var s" + DecToString(tgt) + " := CallDataCopy(s" + DecToString(src) + ");"
    // case CODESIZE       => EnvOp("CODESIZE", CODESIZE)
    case CODECOPY       =>  "var s" + DecToString(tgt) + " := CodeCopy(s" + DecToString(src) + ");"
    // case GASPRICE       => EnvOp("GASPRICE", GASPRICE)
    case EXTCODESIZE    =>  "var s" + DecToString(tgt) + " := ExtCodeSize(s" + DecToString(src) + ");"
    // case EXTCODECOPY    => EnvOp("EXTCODECOPY", EXTCODECOPY)
    case RETURNDATASIZE => "var s" + DecToString(tgt) + " := ReturnDataSize(s" + DecToString(src) + ");"
    case RETURNDATACOPY => "var s" + DecToString(tgt) + " := ReturnDataCopy(s" + DecToString(src) + ");"
    // case EXTCODEHASH    => EnvOp("EXTCODEHASH", EXTCODEHASH)
    // // 0x40s: Block Information
    // case BLOCKHASH   => EnvOp("BLOCKHASH", BLOCKHASH)
    // case COINBASE    => EnvOp("COINBASE", COINBASE)
    // case TIMESTAMP   => EnvOp("TIMESTAMP", TIMESTAMP)
    // case NUMBER      => EnvOp("NUMBER", NUMBER)
    // case DIFFICULTY  => EnvOp("DIFFICULTY", DIFFICULTY)
    // case GASLIMIT    => EnvOp("GASLIMIT", GASLIMIT)
    // case CHAINID     => EnvOp("CHAINID", CHAINID)
    case SELFBALANCE => "var s" + DecToString(tgt) + " := SelfBalance(s" + DecToString(src) + ");"      
    // case BASEFEE     => EnvOp("BASEFEE", BASEFEE)
    // // 0x50s: Stack, Memory, Storage and Flow
    case POP      => "var s" + DecToString(tgt) + " := Pop(s" + DecToString(src) + ");"
    case MLOAD    =>  "var s" + DecToString(tgt) + " := MLoad(s" + DecToString(src) + ");"
    case MSTORE   =>  "var s" + DecToString(tgt) + " := MStore(s" + DecToString(src) + ");"
    case MSTORE8  =>  "var s" + DecToString(tgt) + " := MStore8(s" + DecToString(src) + ");"
    case SLOAD    =>  "var s" + DecToString(tgt) + " := SLoad(s" + DecToString(src) + ");"
    case SSTORE   =>
    //   "assume s" + DecToString(src) + ".WritesPermitted();\n" +
      "var s" + DecToString(tgt) + " := SStore(s" + DecToString(src) + ");"
    case JUMP     =>
    //   "assume s" + DecToString(src) + ".IsJumpDest(s" + DecToString(src) + ".Peek(0)) ;\n" +
      "var s" + DecToString(tgt) + " := Jump(s" + DecToString(src) + ");"
    case JUMPI    =>
    //   "assume s" + DecToString(src) + ".IsJumpDest(s" + DecToString(src) + ".Peek(0)) ;\n" +
      "var s" + DecToString(tgt) + " := JumpI(s" + DecToString(src) + ");"
    // case RJUMP     => JumpOp("RJUMP", RJUMP, 0, 1, 0, 1)
    // case RJUMPI    => JumpOp("RJUMPI", RJUMPI, 0, 2, 0, 2)
    // case RJUMPV    => JumpOp("RJUMPV", RJUMPV, 0, 2, 0, 2)
    // case PC       => RunOp("PC", PC, 1, 0, 1, 0)
    // case MSIZE    => RunOp("MSIZE", MSIZE, 1, 0, 1, 0)
    case GAS      =>
    //   "assume s" + DecToString(src) + ".Gas() <= MAX_U256;\n" +
      "var s" + DecToString(tgt) + " := Gas(s" + DecToString(src) + ");"
    case JUMPDEST => "var s" + DecToString(tgt) + " := JumpDest(s" + DecToString(src) + ");"
    case PUSH0    => "var s" + DecToString(tgt) + " := Push0(s" + DecToString(src) + ");"
    // // 0x60s & 0x70s: Push operations
    case PUSH1 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 1, 0x" + i.arg + ");"
    case PUSH2 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 2, 0x" + i.arg + ");"
    case PUSH3 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 3, 0x" + i.arg + ");"
    case PUSH4 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 4, 0x" + i.arg + ");"
    case PUSH5 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 5, 0x" + i.arg + ");"
    case PUSH6 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 6, 0x" + i.arg + ");"
    case PUSH7 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 7, 0x" + i.arg + ");"
    case PUSH9 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 9, 0x" + i.arg + ");"
    // case PUSH2 => StackOp("PUSH2", PUSH2, 1, 0, 1, 0)
    // case PUSH3 => StackOp("PUSH3", PUSH3, 1, 0, 1, 0)
    // case PUSH4 => StackOp("PUSH4", PUSH4, 1, 0, 1, 0)
    // case PUSH5 => StackOp("PUSH5", PUSH5, 1, 0, 1, 0)
    // case PUSH6 => StackOp("PUSH6", PUSH6, 1, 0, 1, 0)
    // case PUSH7 => StackOp("PUSH7", PUSH7, 1, 0, 1, 0)
    case PUSH8 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 8, 0x" + i.arg + ");"
    // case PUSH9 => StackOp("PUSH9", PUSH9, 1, 0, 1, 0)
    // case PUSH10 => StackOp("PUSH10", PUSH10, 1, 0, 1, 0)
    // case PUSH11 => StackOp("PUSH11", PUSH11, 1, 0, 1, 0)
    // case PUSH12 => StackOp("PUSH12", PUSH12, 1, 0, 1, 0)
    // case PUSH13 => StackOp("PUSH13", PUSH13, 1, 0, 1, 0)
    // case PUSH14 => StackOp("PUSH14", PUSH14, 1, 0, 1, 0)
    case PUSH14 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 14, 0x" + i.arg + ");"
    // case PUSH15 => StackOp("PUSH15", PUSH15, 1, 0, 1, 0)
    // case PUSH16 => StackOp("PUSH16", PUSH16, 1, 0, 1, 0)
    case PUSH16 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 16, 0x" + i.arg + ");"
    // case PUSH17 => StackOp("PUSH17", PUSH17, 1, 0, 1, 0)
    // case PUSH18 => StackOp("PUSH18", PUSH18, 1, 0, 1, 0)
    // case PUSH19 => StackOp("PUSH19", PUSH19, 1, 0, 1, 0)
    // case PUSH20 => StackOp("PUSH20", PUSH20, 1, 0, 1, 0)
    case PUSH20 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 20, 0x" + i.arg + ");"
    // case PUSH21 => StackOp("PUSH21", PUSH21, 1, 0, 1, 0)
    // case PUSH22 => StackOp("PUSH22", PUSH22, 1, 0, 1, 0)
    // case PUSH23 => StackOp("PUSH23", PUSH23, 1, 0, 1, 0)
    // case PUSH24 => StackOp("PUSH24", PUSH24, 1, 0, 1, 0)
    // case PUSH25 => StackOp("PUSH25", PUSH25, 1, 0, 1, 0)
    // case PUSH26 => StackOp("PUSH26", PUSH26, 1, 0, 1, 0)
    // case PUSH27 => StackOp("PUSH27", PUSH27, 1, 0, 1, 0)
    // case PUSH28 => StackOp("PUSH28", PUSH28, 1, 0, 1, 0)
    case PUSH29 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 29, 0x" + i.arg + ");"
    case PUSH30 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 30, 0x" + i.arg + ");"
    case PUSH31 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 31, 0x" + i.arg + ");"
    case PUSH32 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 32, 0x" + i.arg + ");"
    // // 0x80s: Duplicate operations
    case DUP1 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 1);"
    case DUP2 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 2);"
    case DUP3 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 3);"
    case DUP4 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 4);"
    case DUP5 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 5);"
    case DUP6 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 6);"
    case DUP7 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 7);"
    case DUP8 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 8);"
    case DUP9 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 9);"
    case DUP10 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 10);"
    case DUP11 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 11);"
    case DUP12 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 12);"
    case DUP13 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 13);"
    case DUP14 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 14);"
    case DUP15 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 15);"
    case DUP16 => "var s" + DecToString(tgt) + " := Dup(s" + DecToString(src) + ", 16);"
    // // 0x90s: Exchange operations
    case SWAP1 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 1);"
    case SWAP2 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 2);"
    case SWAP3 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 3);"
    case SWAP4 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 4);"
    case SWAP5 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 5);"
    case SWAP6 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 6);"
    case SWAP7 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 7);"
    case SWAP8 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 8);"
    case SWAP9 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 9);"
    case SWAP10 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 10);"
    case SWAP11 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 11);"
    case SWAP12 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 12);"
    case SWAP13 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 13);"
    case SWAP14 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 14);"
    case SWAP15 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 15);"
    case SWAP16 => "var s" + DecToString(tgt) + " := Swap(s" + DecToString(src) + ", 16);"
    // // 0xA0s: Log operations
    case LOG0 => "var s" + DecToString(tgt) + " := LogN(s" + DecToString(src) + ", 0);"
    case LOG1 =>  "var s" + DecToString(tgt) + " := LogN(s" + DecToString(src) + ", 1);"
    case LOG2 =>  "var s" + DecToString(tgt) + " := LogN(s" + DecToString(src) + ", 2);"
    case LOG3 =>  "var s" + DecToString(tgt) + " := LogN(s" + DecToString(src) + ", 3);"
    case LOG4 =>  "var s" + DecToString(tgt) + " := LogN(s" + DecToString(src) + ", 4);"
    // // 0xf0
    // case CREATE => SysOp("CREATE", CREATE, 3, 0, 2, 3)
    // //  @todo: verify call efeect on stack
    case CALL => "var s" + DecToString(tgt) + " := Call(s" + DecToString(src) + ");"
    // case CALLCODE => SysOp("CALLCODE", CALLCODE, 0, 7, 7, 7)
    case RETURN => "var s" + DecToString(tgt) + " := Return(s" + DecToString(src) + ");"
    // case DELEGATECALL => SysOp("DELEGATECALL", DELEGATECALL, 0, 6, 0, 6)
    // case CREATE2 => SysOp("CREATE2", CREATE2)
    case STATICCALL => "var s" + DecToString(tgt) + " := StaticCall(s" + DecToString(src) + ");"
    case REVERT => "var s" + DecToString(tgt) + " := Revert(s" + DecToString(src) + ");"
    // case SELFDESTRUCT => SysOp("SELFDESTRUCT", SELFDESTRUCT)
    case INVALID => "var s" + DecToString(tgt) + " := Stop(s" + DecToString(src) + "); // Invalid instruction:\n"
    case _ => "Unknown instruction:" + i.op.name
  }

  /**
    *  Encode a decimal number into a Hex.
    */
  function DecToChar(n: nat): char
    requires 0 <= n < 10
    ensures '0' <= DecToChar(n) <= '9'
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

  function DecToString(n: nat): string
  {
    if n < 10 then [DecToChar(n)]
    else DecToString(n / 10) + [DecToChar(n % 10)]
  }

}

