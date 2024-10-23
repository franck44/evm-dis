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
    case SLT    => "var s" + DecToString(tgt) + " := SLt(s" + DecToString(src) + ");"
    case SGT    => "var s" + DecToString(tgt) + " := SGt(s" + DecToString(src) + ");"
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
    case ADDRESS        => "var s" + DecToString(tgt) + " := Address(s" + DecToString(src) + ");"
    case BALANCE        => "var s" + DecToString(tgt) + " := Balance(s" + DecToString(src) + ");"
    case ORIGIN         => "var s" + DecToString(tgt) + " := Origin(s" + DecToString(src) + ");"
    case CALLER         => "var s" + DecToString(tgt) + " := Caller(s" + DecToString(src) + ");"
    case CALLVALUE      => "var s" + DecToString(tgt) + " := CallValue(s" + DecToString(src) + ");"
    case CALLDATALOAD   => "var s" + DecToString(tgt) + " := CallDataLoad(s" + DecToString(src) + ");"
    case CALLDATASIZE   => "var s" + DecToString(tgt) + " := CallDataSize(s" + DecToString(src) + ");"
    case CALLDATACOPY   => "var s" + DecToString(tgt) + " := CallDataCopy(s" + DecToString(src) + ");"
    case CODESIZE       => "var s" + DecToString(tgt) + " := CodeSize(s" + DecToString(src) + ");"
    case CODECOPY       => "var s" + DecToString(tgt) + " := CodeCopy(s" + DecToString(src) + ");"
    case GASPRICE       => "var s" + DecToString(tgt) + " := GasPrice(s" + DecToString(src) + ");"
    case EXTCODESIZE    => "var s" + DecToString(tgt) + " := ExtCodeSize(s" + DecToString(src) + ");"
    case EXTCODECOPY    => "var s" + DecToString(tgt) + " := ExtCodeCopy(s" + DecToString(src) + ");"
    case RETURNDATASIZE => "var s" + DecToString(tgt) + " := ReturnDataSize(s" + DecToString(src) + ");"
    case RETURNDATACOPY => "var s" + DecToString(tgt) + " := ReturnDataCopy(s" + DecToString(src) + ");"
    case EXTCODEHASH    => "var s" + DecToString(tgt) + " := ExtCodeHash(s" + DecToString(src) + ");"
    // // 0x40s: Block Information
    case BLOCKHASH   => "var s" + DecToString(tgt) + " := BlockHash(s" + DecToString(src) + ");"
    case COINBASE    => "var s" + DecToString(tgt) + " := CoinBase(s" + DecToString(src) + ");"
    case TIMESTAMP   => "var s" + DecToString(tgt) + " := TimeStamp(s" + DecToString(src) + ");"
    case NUMBER      => "var s" + DecToString(tgt) + " := Number(s" + DecToString(src) + ");"
    case DIFFICULTY  => "var s" + DecToString(tgt) + " := Difficulty(s" + DecToString(src) + ");"
    case GASLIMIT    => "var s" + DecToString(tgt) + " := GasLimit(s" + DecToString(src) + ");"
    case CHAINID     => "var s" + DecToString(tgt) + " := ChainID(s" + DecToString(src) + ");"
    case SELFBALANCE => "var s" + DecToString(tgt) + " := SelfBalance(s" + DecToString(src) + ");"
    case BASEFEE     => "var s" + DecToString(tgt) + " := BaseFee(s" + DecToString(src) + ");"
    // // 0x50s: Stack, Memory, Storage and Flow
    case POP      => "var s" + DecToString(tgt) + " := Pop(s" + DecToString(src) + ");"
    case MLOAD    => "var s" + DecToString(tgt) + " := MLoad(s" + DecToString(src) + ");"
    case MSTORE   => "var s" + DecToString(tgt) + " := MStore(s" + DecToString(src) + ");"
    case MSTORE8  => "var s" + DecToString(tgt) + " := MStore8(s" + DecToString(src) + ");"
    case SLOAD    => "var s" + DecToString(tgt) + " := SLoad(s" + DecToString(src) + ");"
    case SSTORE   => "var s" + DecToString(tgt) + " := SStore(s" + DecToString(src) + ");"
    case JUMP     => "var s" + DecToString(tgt) + " := Jump(s" + DecToString(src) + ");"
    case JUMPI    => "var s" + DecToString(tgt) + " := JumpI(s" + DecToString(src) + ");"
    case RJUMP    => "var s" + DecToString(tgt) + " := RJump(s" + DecToString(src) + ");"
    case RJUMPI   => "var s" + DecToString(tgt) + " := RJumpI(s" + DecToString(src) + ");"
    case RJUMPV   => "var s" + DecToString(tgt) + " := RJumpV(s" + DecToString(src) + ");"
    case PC       => "var s" + DecToString(tgt) + " := PC(s" + DecToString(src) + ");"
    case MSIZE    => "var s" + DecToString(tgt) + " := MSize(s" + DecToString(src) + ");"
    case GAS      => "var s" + DecToString(tgt) + " := Gas(s" + DecToString(src) + ");"
    case JUMPDEST => "var s" + DecToString(tgt) + " := JumpDest(s" + DecToString(src) + ");"
    case PUSH0    => "var s" + DecToString(tgt) + " := Push0(s" + DecToString(src) + ");"
    // // 0x60s & 0x70s: Push operations
    case PUSH1 => "var s" + DecToString(tgt) + " := Push1(s" + DecToString(src) + ", 0x" + i.arg + ");"
    case PUSH2 => "var s" + DecToString(tgt) + " := Push2(s" + DecToString(src) + ", 0x" + i.arg + ");"
    case PUSH3 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 3, 0x" + i.arg + ");"
    case PUSH4 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 4, 0x" + i.arg + ");"
    case PUSH5 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 5, 0x" + i.arg + ");"
    case PUSH6 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 6, 0x" + i.arg + ");"
    case PUSH7 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 7, 0x" + i.arg + ");"
    case PUSH8 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 8, 0x" + i.arg + ");"
    case PUSH9 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 9, 0x" + i.arg + ");"
    case PUSH10 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 10, 0x" + i.arg + ");"
    case PUSH11 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 11, 0x" + i.arg + ");"
    case PUSH12 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 12, 0x" + i.arg + ");"
    case PUSH13 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 13, 0x" + i.arg + ");"
    case PUSH14 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 14, 0x" + i.arg + ");"
    case PUSH15 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 15, 0x" + i.arg + ");"
    case PUSH16 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 16, 0x" + i.arg + ");"
    case PUSH17 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 17, 0x" + i.arg + ");"
    case PUSH18 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 18, 0x" + i.arg + ");"
    case PUSH19 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 19, 0x" + i.arg + ");"
    case PUSH20 => "var s" + DecToString(tgt) + " := Push20(s" + DecToString(src) + ", 0x" + i.arg + ");"
    case PUSH21 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 21, 0x" + i.arg + ");"
    case PUSH22 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 22, 0x" + i.arg + ");"
    case PUSH23 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 23, 0x" + i.arg + ");"
    case PUSH24 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 24, 0x" + i.arg + ");"
    case PUSH25 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 25, 0x" + i.arg + ");"
    case PUSH26 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 26, 0x" + i.arg + ");"
    case PUSH27 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 27, 0x" + i.arg + ");"
    case PUSH28 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 28, 0x" + i.arg + ");"
    case PUSH29 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 29, 0x" + i.arg + ");"
    case PUSH30 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 30, 0x" + i.arg + ");"
    case PUSH31 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 31, 0x" + i.arg + ");"
    case PUSH32 => "var s" + DecToString(tgt) + " := PushN(s" + DecToString(src) + ", 32, 0x" + i.arg + ");"
    // // 0x80s: Duplicate operations
    case DUP1 => "var s" + DecToString(tgt) + " := Dup1(s" + DecToString(src) + ");"
    case DUP2 => "var s" + DecToString(tgt) + " := Dup2(s" + DecToString(src) + ");"
    case DUP3 => "var s" + DecToString(tgt) + " := Dup3(s" + DecToString(src) + ");"
    case DUP4 => "var s" + DecToString(tgt) + " := Dup4(s" + DecToString(src) + ");"
    case DUP5 => "var s" + DecToString(tgt) + " := Dup5(s" + DecToString(src) + ");"
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
    case SWAP1 => "var s" + DecToString(tgt) + " := Swap1(s" + DecToString(src) + ");"
    case SWAP2 => "var s" + DecToString(tgt) + " := Swap2(s" + DecToString(src) + ");"
    case SWAP3 => "var s" + DecToString(tgt) + " := Swap3(s" + DecToString(src) + ");"
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
    case CALL => "var s" + DecToString(tgt) + " := Call(s" + DecToString(src) + ");"
    case CALLCODE => "var s" + DecToString(tgt) + " := CallCode(s" + DecToString(src) + ");"
    case RETURN => "var s" + DecToString(tgt) + " := Return(s" + DecToString(src) + ");"
    case DELEGATECALL => "var s" + DecToString(tgt) + " := DelegateCall(s" + DecToString(src) + ");"
    case CREATE2 => "var s" + DecToString(tgt) + " := Create2(s" + DecToString(src) + ");"
    case STATICCALL => "var s" + DecToString(tgt) + " := StaticCall(s" + DecToString(src) + ");"
    case REVERT => "var s" + DecToString(tgt) + " := Revert(s" + DecToString(src) + ");"
    case SELFDESTRUCT => "var s" + DecToString(tgt) + " := SelfDestruct(s" + DecToString(src) + ");"
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

