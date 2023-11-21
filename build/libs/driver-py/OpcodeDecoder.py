import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Int
import MiscTypes
import EVMConstants
import EVMOpcodes

# Module: OpcodeDecoder

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Decode(op):
        if (op) == (0):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "STOP")), EVMConstants.default__.STOP, 0, 0, 0, 0)
        elif (op) == (1):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ADD")), EVMConstants.default__.ADD, 0, 2, 1, 2)
        elif (op) == (2):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MUL")), EVMConstants.default__.MUL, 0, 2, 1, 2)
        elif (op) == (3):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SUB")), EVMConstants.default__.SUB, 0, 2, 1, 2)
        elif (op) == (4):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DIV")), EVMConstants.default__.DIV, 0, 2, 1, 2)
        elif (op) == (5):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SDIV")), EVMConstants.default__.SDIV, 0, 2, 1, 2)
        elif (op) == (6):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MOD")), EVMConstants.default__.MOD, 0, 2, 1, 2)
        elif (op) == (7):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SMOD")), EVMConstants.default__.SMOD, 0, 2, 1, 2)
        elif (op) == (8):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ADDMOD")), EVMConstants.default__.ADDMOD, 0, 2, 1, 2)
        elif (op) == (9):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MULMOD")), EVMConstants.default__.MULMOD, 0, 2, 1, 2)
        elif (op) == (10):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EXP")), EVMConstants.default__.EXP, 0, 2, 1, 2)
        elif (op) == (11):
            return EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SIGNEXTEND")), EVMConstants.default__.SIGNEXTEND, 0, 2, 1, 2)
        elif (op) == (16):
            return EVMOpcodes.Opcode_CompOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LT")), EVMConstants.default__.LT, 0, 2, 1, 2)
        elif (op) == (17):
            return EVMOpcodes.Opcode_CompOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "GT")), EVMConstants.default__.GT, 0, 2, 1, 2)
        elif (op) == (18):
            return EVMOpcodes.Opcode_CompOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SLT")), EVMConstants.default__.SLT, 0, 2, 1, 2)
        elif (op) == (19):
            return EVMOpcodes.Opcode_CompOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SGT")), EVMConstants.default__.SGT, 0, 2, 1, 2)
        elif (op) == (20):
            return EVMOpcodes.Opcode_CompOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EQ")), EVMConstants.default__.EQ, 0, 2, 1, 2)
        elif (op) == (21):
            return EVMOpcodes.Opcode_CompOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ISZERO")), EVMConstants.default__.ISZERO, 0, 1, 1, 1)
        elif (op) == (22):
            return EVMOpcodes.Opcode_BitwiseOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "AND")), EVMConstants.default__.AND, 0, 2, 1, 2)
        elif (op) == (23):
            return EVMOpcodes.Opcode_BitwiseOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "OR")), EVMConstants.default__.OR, 0, 2, 1, 2)
        elif (op) == (24):
            return EVMOpcodes.Opcode_BitwiseOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "XOR")), EVMConstants.default__.XOR, 0, 2, 1, 2)
        elif (op) == (25):
            return EVMOpcodes.Opcode_BitwiseOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "NOT")), EVMConstants.default__.NOT, 0, 1, 1, 1)
        elif (op) == (26):
            return EVMOpcodes.Opcode_BitwiseOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BYTE")), EVMConstants.default__.BYTE, 0, 2, 1, 2)
        elif (op) == (27):
            return EVMOpcodes.Opcode_BitwiseOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SHL")), EVMConstants.default__.SHL, 0, 2, 1, 2)
        elif (op) == (28):
            return EVMOpcodes.Opcode_BitwiseOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SHR")), EVMConstants.default__.SHR, 0, 2, 1, 2)
        elif (op) == (29):
            return EVMOpcodes.Opcode_BitwiseOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SAR")), EVMConstants.default__.SAR, 0, 2, 1, 2)
        elif (op) == (32):
            return EVMOpcodes.Opcode_KeccakOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "KECCAK256")), EVMConstants.default__.KECCAK256, 0, 2, 1, 2)
        elif (op) == (48):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ADDRESS")), EVMConstants.default__.ADDRESS, 1, 0, 1, 0)
        elif (op) == (49):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BALANCE")), EVMConstants.default__.BALANCE, 0, 1, 1, 1)
        elif (op) == (50):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ORIGIN")), EVMConstants.default__.ORIGIN, 1, 0, 1, 0)
        elif (op) == (51):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CALLER")), EVMConstants.default__.CALLER, 1, 0, 1, 0)
        elif (op) == (52):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CALLVALUE")), EVMConstants.default__.CALLVALUE, 1, 0, 1, 0)
        elif (op) == (53):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CALLDATALOAD")), EVMConstants.default__.CALLDATALOAD, 0, 1, 1, 1)
        elif (op) == (54):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CALLDATASIZE")), EVMConstants.default__.CALLDATASIZE, 1, 0, 1, 0)
        elif (op) == (55):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CALLDATACOPY")), EVMConstants.default__.CALLDATACOPY, 0, 3, 0, 3)
        elif (op) == (56):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CODESIZE")), EVMConstants.default__.CODESIZE, 1, 0, 1, 0)
        elif (op) == (57):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CODECOPY")), EVMConstants.default__.CODECOPY, 0, 3, 0, 3)
        elif (op) == (58):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "GASPRICE")), EVMConstants.default__.GASPRICE, 1, 0, 1, 0)
        elif (op) == (59):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EXTCODESIZE")), EVMConstants.default__.EXTCODESIZE, 0, 1, 1, 1)
        elif (op) == (60):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EXTCODECOPY")), EVMConstants.default__.EXTCODECOPY, 0, 4, 0, 4)
        elif (op) == (61):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RETURNDATASIZE")), EVMConstants.default__.RETURNDATASIZE, 1, 0, 1, 0)
        elif (op) == (62):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RETURNDATACOPY")), EVMConstants.default__.RETURNDATACOPY, 0, 3, 0, 3)
        elif (op) == (63):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EXTCODEHASH")), EVMConstants.default__.EXTCODEHASH, 0, 1, 1, 1)
        elif (op) == (64):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BLOCKHASH")), EVMConstants.default__.BLOCKHASH, 0, 1, 1, 1)
        elif (op) == (65):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "COINBASE")), EVMConstants.default__.COINBASE, 1, 0, 1, 0)
        elif (op) == (66):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "TIMESTAMP")), EVMConstants.default__.TIMESTAMP, 1, 0, 1, 0)
        elif (op) == (67):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "NUMBER")), EVMConstants.default__.NUMBER, 1, 0, 1, 0)
        elif (op) == (68):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DIFFICULTY")), EVMConstants.default__.DIFFICULTY, 1, 0, 1, 0)
        elif (op) == (69):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "GASLIMIT")), EVMConstants.default__.GASLIMIT, 1, 0, 1, 0)
        elif (op) == (70):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CHAINID")), EVMConstants.default__.CHAINID, 1, 0, 1, 0)
        elif (op) == (71):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SELFBALANCE")), EVMConstants.default__.SELFBALANCE, 1, 0, 1, 0)
        elif (op) == (72):
            return EVMOpcodes.Opcode_EnvOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BASEFEE")), EVMConstants.default__.BASEFEE, 1, 0, 1, 0)
        elif (op) == (80):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "POP")), EVMConstants.default__.POP, 0, 1, 0, 1)
        elif (op) == (81):
            return EVMOpcodes.Opcode_MemOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MLOAD")), EVMConstants.default__.MLOAD, 0, 1, 1, 1)
        elif (op) == (82):
            return EVMOpcodes.Opcode_MemOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MSTORE")), EVMConstants.default__.MSTORE, 0, 2, 0, 2)
        elif (op) == (83):
            return EVMOpcodes.Opcode_MemOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MSTORE8")), EVMConstants.default__.MSTORE8, 0, 2, 0, 2)
        elif (op) == (84):
            return EVMOpcodes.Opcode_StorageOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SLOAD")), EVMConstants.default__.SLOAD, 0, 1, 1, 1)
        elif (op) == (85):
            return EVMOpcodes.Opcode_StorageOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SSTORE")), EVMConstants.default__.SSTORE, 0, 2, 0, 2)
        elif (op) == (86):
            return EVMOpcodes.Opcode_JumpOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMP")), EVMConstants.default__.JUMP, 0, 1, 0, 1)
        elif (op) == (87):
            return EVMOpcodes.Opcode_JumpOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMPI")), EVMConstants.default__.JUMPI, 0, 2, 0, 2)
        elif (op) == (92):
            return EVMOpcodes.Opcode_JumpOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMP")), EVMConstants.default__.RJUMP, 0, 1, 0, 1)
        elif (op) == (93):
            return EVMOpcodes.Opcode_JumpOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPI")), EVMConstants.default__.RJUMPI, 0, 2, 0, 2)
        elif (op) == (94):
            return EVMOpcodes.Opcode_JumpOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPV")), EVMConstants.default__.RJUMPV, 0, 2, 0, 2)
        elif (op) == (88):
            return EVMOpcodes.Opcode_RunOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PC")), EVMConstants.default__.PC, 1, 0, 1, 0)
        elif (op) == (89):
            return EVMOpcodes.Opcode_RunOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MSIZE")), EVMConstants.default__.MSIZE, 1, 0, 1, 0)
        elif (op) == (90):
            return EVMOpcodes.Opcode_RunOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "GAS")), EVMConstants.default__.GAS, 1, 0, 1, 0)
        elif (op) == (91):
            return EVMOpcodes.Opcode_JumpOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMPDEST")), EVMConstants.default__.JUMPDEST, 0, 0, 0, 0)
        elif (op) == (95):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH0")), EVMConstants.default__.PUSH0, 1, 0, 1, 0)
        elif (op) == (96):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH1")), EVMConstants.default__.PUSH1, 1, 0, 1, 0)
        elif (op) == (97):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH2")), EVMConstants.default__.PUSH2, 1, 0, 1, 0)
        elif (op) == (98):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH3")), EVMConstants.default__.PUSH3, 1, 0, 1, 0)
        elif (op) == (99):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH4")), EVMConstants.default__.PUSH4, 1, 0, 1, 0)
        elif (op) == (100):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH5")), EVMConstants.default__.PUSH5, 1, 0, 1, 0)
        elif (op) == (101):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH6")), EVMConstants.default__.PUSH6, 1, 0, 1, 0)
        elif (op) == (102):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH7")), EVMConstants.default__.PUSH7, 1, 0, 1, 0)
        elif (op) == (103):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH8")), EVMConstants.default__.PUSH8, 1, 0, 1, 0)
        elif (op) == (104):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH9")), EVMConstants.default__.PUSH9, 1, 0, 1, 0)
        elif (op) == (105):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH10")), EVMConstants.default__.PUSH10, 1, 0, 1, 0)
        elif (op) == (106):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH11")), EVMConstants.default__.PUSH11, 1, 0, 1, 0)
        elif (op) == (107):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH12")), EVMConstants.default__.PUSH12, 1, 0, 1, 0)
        elif (op) == (108):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH13")), EVMConstants.default__.PUSH13, 1, 0, 1, 0)
        elif (op) == (109):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH14")), EVMConstants.default__.PUSH14, 1, 0, 1, 0)
        elif (op) == (110):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH15")), EVMConstants.default__.PUSH15, 1, 0, 1, 0)
        elif (op) == (111):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH16")), EVMConstants.default__.PUSH16, 1, 0, 1, 0)
        elif (op) == (112):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH17")), EVMConstants.default__.PUSH17, 1, 0, 1, 0)
        elif (op) == (113):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH18")), EVMConstants.default__.PUSH18, 1, 0, 1, 0)
        elif (op) == (114):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH19")), EVMConstants.default__.PUSH19, 1, 0, 1, 0)
        elif (op) == (115):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH20")), EVMConstants.default__.PUSH20, 1, 0, 1, 0)
        elif (op) == (116):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH21")), EVMConstants.default__.PUSH21, 1, 0, 1, 0)
        elif (op) == (117):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH22")), EVMConstants.default__.PUSH22, 1, 0, 1, 0)
        elif (op) == (118):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH23")), EVMConstants.default__.PUSH23, 1, 0, 1, 0)
        elif (op) == (119):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH24")), EVMConstants.default__.PUSH24, 1, 0, 1, 0)
        elif (op) == (120):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH25")), EVMConstants.default__.PUSH25, 1, 0, 1, 0)
        elif (op) == (121):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH26")), EVMConstants.default__.PUSH26, 1, 0, 1, 0)
        elif (op) == (122):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH27")), EVMConstants.default__.PUSH27, 1, 0, 1, 0)
        elif (op) == (123):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH28")), EVMConstants.default__.PUSH28, 1, 0, 1, 0)
        elif (op) == (124):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH29")), EVMConstants.default__.PUSH29, 1, 0, 1, 0)
        elif (op) == (125):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH30")), EVMConstants.default__.PUSH30, 1, 0, 1, 0)
        elif (op) == (126):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH31")), EVMConstants.default__.PUSH31, 1, 0, 1, 0)
        elif (op) == (127):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PUSH32")), EVMConstants.default__.PUSH32, 1, 0, 1, 0)
        elif (op) == (128):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP1")), EVMConstants.default__.DUP1, 1, 1, 1, 0)
        elif (op) == (129):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP2")), EVMConstants.default__.DUP2, 1, 2, 1, 0)
        elif (op) == (130):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP3")), EVMConstants.default__.DUP3, 1, 3, 1, 0)
        elif (op) == (131):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP4")), EVMConstants.default__.DUP4, 1, 4, 1, 0)
        elif (op) == (132):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP5")), EVMConstants.default__.DUP5, 1, 5, 1, 0)
        elif (op) == (133):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP6")), EVMConstants.default__.DUP6, 1, 6, 1, 0)
        elif (op) == (134):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP7")), EVMConstants.default__.DUP7, 1, 7, 1, 0)
        elif (op) == (135):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP8")), EVMConstants.default__.DUP8, 1, 8, 1, 0)
        elif (op) == (136):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP9")), EVMConstants.default__.DUP9, 1, 9, 1, 0)
        elif (op) == (137):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP10")), EVMConstants.default__.DUP10, 1, 10, 1, 0)
        elif (op) == (138):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP11")), EVMConstants.default__.DUP11, 1, 11, 1, 0)
        elif (op) == (139):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP12")), EVMConstants.default__.DUP12, 1, 12, 1, 0)
        elif (op) == (140):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP13")), EVMConstants.default__.DUP13, 1, 13, 1, 0)
        elif (op) == (141):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP14")), EVMConstants.default__.DUP14, 1, 14, 1, 0)
        elif (op) == (142):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP15")), EVMConstants.default__.DUP15, 1, 15, 1, 0)
        elif (op) == (143):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DUP16")), EVMConstants.default__.DUP16, 1, 16, 1, 0)
        elif (op) == (144):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP1")), EVMConstants.default__.SWAP1, 0, (1) + (1), 0, 0)
        elif (op) == (145):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP2")), EVMConstants.default__.SWAP2, 0, (2) + (1), 0, 0)
        elif (op) == (146):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP3")), EVMConstants.default__.SWAP3, 0, (3) + (1), 0, 0)
        elif (op) == (147):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP4")), EVMConstants.default__.SWAP4, 0, (4) + (1), 0, 0)
        elif (op) == (148):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP5")), EVMConstants.default__.SWAP5, 0, (5) + (1), 0, 0)
        elif (op) == (149):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP6")), EVMConstants.default__.SWAP6, 0, (6) + (1), 0, 0)
        elif (op) == (150):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP7")), EVMConstants.default__.SWAP7, 0, (7) + (1), 0, 0)
        elif (op) == (151):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP8")), EVMConstants.default__.SWAP8, 0, (8) + (1), 0, 0)
        elif (op) == (152):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP9")), EVMConstants.default__.SWAP9, 0, (9) + (1), 0, 0)
        elif (op) == (153):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP10")), EVMConstants.default__.SWAP10, 0, (10) + (1), 0, 0)
        elif (op) == (154):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP11")), EVMConstants.default__.SWAP11, 0, (11) + (1), 0, 0)
        elif (op) == (155):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP12")), EVMConstants.default__.SWAP12, 0, (12) + (1), 0, 0)
        elif (op) == (156):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP13")), EVMConstants.default__.SWAP13, 0, (13) + (1), 0, 0)
        elif (op) == (157):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP14")), EVMConstants.default__.SWAP14, 0, (14) + (1), 0, 0)
        elif (op) == (158):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP15")), EVMConstants.default__.SWAP15, 0, (15) + (1), 0, 0)
        elif (op) == (159):
            return EVMOpcodes.Opcode_StackOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SWAP16")), EVMConstants.default__.SWAP16, 0, (16) + (1), 0, 0)
        elif (op) == (160):
            return EVMOpcodes.Opcode_LogOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LOG0")), EVMConstants.default__.LOG0, 0, (0) + (2), 0, (0) + (2))
        elif (op) == (161):
            return EVMOpcodes.Opcode_LogOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LOG1")), EVMConstants.default__.LOG1, 0, (1) + (2), 0, (1) + (2))
        elif (op) == (162):
            return EVMOpcodes.Opcode_LogOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LOG2")), EVMConstants.default__.LOG2, 0, (2) + (2), 0, (2) + (2))
        elif (op) == (163):
            return EVMOpcodes.Opcode_LogOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LOG3")), EVMConstants.default__.LOG3, 0, (3) + (2), 0, (3) + (2))
        elif (op) == (164):
            return EVMOpcodes.Opcode_LogOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LOG4")), EVMConstants.default__.LOG4, 0, (4) + (2), 0, (4) + (2))
        elif (op) == (240):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CREATE")), EVMConstants.default__.CREATE, 3, 0, 2, 3)
        elif (op) == (241):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CALL")), EVMConstants.default__.CALL, 1, 7, 1, 7)
        elif (op) == (242):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CALLCODE")), EVMConstants.default__.CALLCODE, 1, 7, 1, 7)
        elif (op) == (243):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RETURN")), EVMConstants.default__.RETURN, 0, 2, 0, 0)
        elif (op) == (244):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "DELEGATECALL")), EVMConstants.default__.DELEGATECALL, 0, 6, 0, 6)
        elif (op) == (245):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CREATE2")), EVMConstants.default__.CREATE2, 0, 0, 0, 0)
        elif (op) == (250):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "STATICCALL")), EVMConstants.default__.STATICCALL, 1, 6, 1, 6)
        elif (op) == (253):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "REVERT")), EVMConstants.default__.REVERT, 0, 2, 0, 0)
        elif (op) == (255):
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SELFDESTRUCT")), EVMConstants.default__.SELFDESTRUCT, 0, 0, 0, 0)
        elif True:
            return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "INVALID")), EVMConstants.default__.INVALID, 0, 0, 0, 0)

