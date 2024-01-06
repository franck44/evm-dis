import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes
import Int
import EVMConstants
import EVMOpcodes
import OpcodeDecoder
import Hex
import StackElement
import WeakPre
import State
import EVMToolTips
import Instructions

# Module: BinaryDecoder

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Disassemble(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif (len(s)) == (1):
                    return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Odd number of characters ending in "))) + (s), next)]))
                elif True:
                    source42_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source42_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference((s)[:2:]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "' is not an Hex number"))), next)]))
                    elif True:
                        d_647___mcc_h0_ = source42_.v
                        d_648_v_ = d_647___mcc_h0_
                        d_649_op_ = OpcodeDecoder.default__.Decode(d_648_v_)
                        if ((d_649_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_649_op_).Args()))) or (not(Hex.default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_649_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_649_op_).name), next)]))
                            elif True:
                                in33_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_649_op_).Args())::])
                                in34_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_649_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_649_op_).Args()):]), next)]))
                                in35_ = ((next) + (1)) + ((d_649_op_).Args())
                                s = in33_
                                p = in34_
                                next = in35_
                                raise _dafny.TailCall()
                        elif True:
                            in36_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in37_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_649_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in38_ = (next) + (1)
                            s = in36_
                            p = in37_
                            next = in38_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_650_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_650_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_650_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_650_op_).name), next)]))
                        elif True:
                            in39_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_650_op_).Args()::])
                            in40_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_650_op_, Hex.default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_650_op_).Args():])), next)]))
                            in41_ = ((next) + (1)) + ((d_650_op_).Args())
                            s = in39_
                            p = in40_
                            next = in41_
                            raise _dafny.TailCall()
                    elif True:
                        in42_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in43_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_650_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in44_ = (next) + (1)
                        s = in42_
                        p = in43_
                        next = in44_
                        raise _dafny.TailCall()
                break

