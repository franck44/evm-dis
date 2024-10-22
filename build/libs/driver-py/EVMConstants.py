import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import MiscTypes as MiscTypes
import Int as Int

# Module: EVMConstants

class default__:
    def  __init__(self):
        pass

    @_dafny.classproperty
    def STOP(instance):
        return 0
    @_dafny.classproperty
    def ADD(instance):
        return 1
    @_dafny.classproperty
    def MUL(instance):
        return 2
    @_dafny.classproperty
    def SUB(instance):
        return 3
    @_dafny.classproperty
    def DIV(instance):
        return 4
    @_dafny.classproperty
    def SDIV(instance):
        return 5
    @_dafny.classproperty
    def MOD(instance):
        return 6
    @_dafny.classproperty
    def SMOD(instance):
        return 7
    @_dafny.classproperty
    def ADDMOD(instance):
        return 8
    @_dafny.classproperty
    def MULMOD(instance):
        return 9
    @_dafny.classproperty
    def EXP(instance):
        return 10
    @_dafny.classproperty
    def SIGNEXTEND(instance):
        return 11
    @_dafny.classproperty
    def LT(instance):
        return 16
    @_dafny.classproperty
    def GT(instance):
        return 17
    @_dafny.classproperty
    def SLT(instance):
        return 18
    @_dafny.classproperty
    def SGT(instance):
        return 19
    @_dafny.classproperty
    def EQ(instance):
        return 20
    @_dafny.classproperty
    def ISZERO(instance):
        return 21
    @_dafny.classproperty
    def AND(instance):
        return 22
    @_dafny.classproperty
    def OR(instance):
        return 23
    @_dafny.classproperty
    def XOR(instance):
        return 24
    @_dafny.classproperty
    def NOT(instance):
        return 25
    @_dafny.classproperty
    def BYTE(instance):
        return 26
    @_dafny.classproperty
    def SHL(instance):
        return 27
    @_dafny.classproperty
    def SHR(instance):
        return 28
    @_dafny.classproperty
    def SAR(instance):
        return 29
    @_dafny.classproperty
    def KECCAK256(instance):
        return 32
    @_dafny.classproperty
    def ADDRESS(instance):
        return 48
    @_dafny.classproperty
    def BALANCE(instance):
        return 49
    @_dafny.classproperty
    def ORIGIN(instance):
        return 50
    @_dafny.classproperty
    def CALLER(instance):
        return 51
    @_dafny.classproperty
    def CALLVALUE(instance):
        return 52
    @_dafny.classproperty
    def CALLDATALOAD(instance):
        return 53
    @_dafny.classproperty
    def CALLDATASIZE(instance):
        return 54
    @_dafny.classproperty
    def CALLDATACOPY(instance):
        return 55
    @_dafny.classproperty
    def CODESIZE(instance):
        return 56
    @_dafny.classproperty
    def CODECOPY(instance):
        return 57
    @_dafny.classproperty
    def GASPRICE(instance):
        return 58
    @_dafny.classproperty
    def EXTCODESIZE(instance):
        return 59
    @_dafny.classproperty
    def EXTCODECOPY(instance):
        return 60
    @_dafny.classproperty
    def RETURNDATASIZE(instance):
        return 61
    @_dafny.classproperty
    def RETURNDATACOPY(instance):
        return 62
    @_dafny.classproperty
    def EXTCODEHASH(instance):
        return 63
    @_dafny.classproperty
    def BLOCKHASH(instance):
        return 64
    @_dafny.classproperty
    def COINBASE(instance):
        return 65
    @_dafny.classproperty
    def TIMESTAMP(instance):
        return 66
    @_dafny.classproperty
    def NUMBER(instance):
        return 67
    @_dafny.classproperty
    def DIFFICULTY(instance):
        return 68
    @_dafny.classproperty
    def GASLIMIT(instance):
        return 69
    @_dafny.classproperty
    def CHAINID(instance):
        return 70
    @_dafny.classproperty
    def SELFBALANCE(instance):
        return 71
    @_dafny.classproperty
    def BASEFEE(instance):
        return 72
    @_dafny.classproperty
    def POP(instance):
        return 80
    @_dafny.classproperty
    def MLOAD(instance):
        return 81
    @_dafny.classproperty
    def MSTORE(instance):
        return 82
    @_dafny.classproperty
    def MSTORE8(instance):
        return 83
    @_dafny.classproperty
    def SLOAD(instance):
        return 84
    @_dafny.classproperty
    def SSTORE(instance):
        return 85
    @_dafny.classproperty
    def JUMP(instance):
        return 86
    @_dafny.classproperty
    def JUMPI(instance):
        return 87
    @_dafny.classproperty
    def PC(instance):
        return 88
    @_dafny.classproperty
    def MSIZE(instance):
        return 89
    @_dafny.classproperty
    def GAS(instance):
        return 90
    @_dafny.classproperty
    def JUMPDEST(instance):
        return 91
    @_dafny.classproperty
    def RJUMP(instance):
        return 92
    @_dafny.classproperty
    def RJUMPI(instance):
        return 93
    @_dafny.classproperty
    def RJUMPV(instance):
        return 94
    @_dafny.classproperty
    def PUSH0(instance):
        return 95
    @_dafny.classproperty
    def PUSH1(instance):
        return 96
    @_dafny.classproperty
    def PUSH2(instance):
        return 97
    @_dafny.classproperty
    def PUSH3(instance):
        return 98
    @_dafny.classproperty
    def PUSH4(instance):
        return 99
    @_dafny.classproperty
    def PUSH5(instance):
        return 100
    @_dafny.classproperty
    def PUSH6(instance):
        return 101
    @_dafny.classproperty
    def PUSH7(instance):
        return 102
    @_dafny.classproperty
    def PUSH8(instance):
        return 103
    @_dafny.classproperty
    def PUSH9(instance):
        return 104
    @_dafny.classproperty
    def PUSH10(instance):
        return 105
    @_dafny.classproperty
    def PUSH11(instance):
        return 106
    @_dafny.classproperty
    def PUSH12(instance):
        return 107
    @_dafny.classproperty
    def PUSH13(instance):
        return 108
    @_dafny.classproperty
    def PUSH14(instance):
        return 109
    @_dafny.classproperty
    def PUSH15(instance):
        return 110
    @_dafny.classproperty
    def PUSH16(instance):
        return 111
    @_dafny.classproperty
    def PUSH17(instance):
        return 112
    @_dafny.classproperty
    def PUSH18(instance):
        return 113
    @_dafny.classproperty
    def PUSH19(instance):
        return 114
    @_dafny.classproperty
    def PUSH20(instance):
        return 115
    @_dafny.classproperty
    def PUSH21(instance):
        return 116
    @_dafny.classproperty
    def PUSH22(instance):
        return 117
    @_dafny.classproperty
    def PUSH23(instance):
        return 118
    @_dafny.classproperty
    def PUSH24(instance):
        return 119
    @_dafny.classproperty
    def PUSH25(instance):
        return 120
    @_dafny.classproperty
    def PUSH26(instance):
        return 121
    @_dafny.classproperty
    def PUSH27(instance):
        return 122
    @_dafny.classproperty
    def PUSH28(instance):
        return 123
    @_dafny.classproperty
    def PUSH29(instance):
        return 124
    @_dafny.classproperty
    def PUSH30(instance):
        return 125
    @_dafny.classproperty
    def PUSH31(instance):
        return 126
    @_dafny.classproperty
    def PUSH32(instance):
        return 127
    @_dafny.classproperty
    def DUP1(instance):
        return 128
    @_dafny.classproperty
    def DUP2(instance):
        return 129
    @_dafny.classproperty
    def DUP3(instance):
        return 130
    @_dafny.classproperty
    def DUP4(instance):
        return 131
    @_dafny.classproperty
    def DUP5(instance):
        return 132
    @_dafny.classproperty
    def DUP6(instance):
        return 133
    @_dafny.classproperty
    def DUP7(instance):
        return 134
    @_dafny.classproperty
    def DUP8(instance):
        return 135
    @_dafny.classproperty
    def DUP9(instance):
        return 136
    @_dafny.classproperty
    def DUP10(instance):
        return 137
    @_dafny.classproperty
    def DUP11(instance):
        return 138
    @_dafny.classproperty
    def DUP12(instance):
        return 139
    @_dafny.classproperty
    def DUP13(instance):
        return 140
    @_dafny.classproperty
    def DUP14(instance):
        return 141
    @_dafny.classproperty
    def DUP15(instance):
        return 142
    @_dafny.classproperty
    def DUP16(instance):
        return 143
    @_dafny.classproperty
    def SWAP1(instance):
        return 144
    @_dafny.classproperty
    def SWAP2(instance):
        return 145
    @_dafny.classproperty
    def SWAP3(instance):
        return 146
    @_dafny.classproperty
    def SWAP4(instance):
        return 147
    @_dafny.classproperty
    def SWAP5(instance):
        return 148
    @_dafny.classproperty
    def SWAP6(instance):
        return 149
    @_dafny.classproperty
    def SWAP7(instance):
        return 150
    @_dafny.classproperty
    def SWAP8(instance):
        return 151
    @_dafny.classproperty
    def SWAP9(instance):
        return 152
    @_dafny.classproperty
    def SWAP10(instance):
        return 153
    @_dafny.classproperty
    def SWAP11(instance):
        return 154
    @_dafny.classproperty
    def SWAP12(instance):
        return 155
    @_dafny.classproperty
    def SWAP13(instance):
        return 156
    @_dafny.classproperty
    def SWAP14(instance):
        return 157
    @_dafny.classproperty
    def SWAP15(instance):
        return 158
    @_dafny.classproperty
    def SWAP16(instance):
        return 159
    @_dafny.classproperty
    def LOG0(instance):
        return 160
    @_dafny.classproperty
    def LOG1(instance):
        return 161
    @_dafny.classproperty
    def LOG2(instance):
        return 162
    @_dafny.classproperty
    def LOG3(instance):
        return 163
    @_dafny.classproperty
    def LOG4(instance):
        return 164
    @_dafny.classproperty
    def EOF(instance):
        return 239
    @_dafny.classproperty
    def CREATE(instance):
        return 240
    @_dafny.classproperty
    def CALL(instance):
        return 241
    @_dafny.classproperty
    def CALLCODE(instance):
        return 242
    @_dafny.classproperty
    def RETURN(instance):
        return 243
    @_dafny.classproperty
    def DELEGATECALL(instance):
        return 244
    @_dafny.classproperty
    def CREATE2(instance):
        return 245
    @_dafny.classproperty
    def STATICCALL(instance):
        return 250
    @_dafny.classproperty
    def REVERT(instance):
        return 253
    @_dafny.classproperty
    def INVALID(instance):
        return 254
    @_dafny.classproperty
    def SELFDESTRUCT(instance):
        return 255
