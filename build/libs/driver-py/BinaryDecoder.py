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
                        d_646___mcc_h0_ = source42_.v
                        d_647_v_ = d_646___mcc_h0_
                        d_648_op_ = OpcodeDecoder.default__.Decode(d_647_v_)
                        if ((d_648_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_648_op_).Args()))) or (not(Hex.default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_648_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_648_op_).name), next)]))
                            elif True:
                                in29_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_648_op_).Args())::])
                                in30_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_648_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_648_op_).Args()):]), next)]))
                                in31_ = ((next) + (1)) + ((d_648_op_).Args())
                                s = in29_
                                p = in30_
                                next = in31_
                                raise _dafny.TailCall()
                        elif True:
                            in32_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in33_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_648_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in34_ = (next) + (1)
                            s = in32_
                            p = in33_
                            next = in34_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_649_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_649_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_649_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_649_op_).name), next)]))
                        elif True:
                            in35_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_649_op_).Args()::])
                            in36_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_649_op_, Hex.default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_649_op_).Args():])), next)]))
                            in37_ = ((next) + (1)) + ((d_649_op_).Args())
                            s = in35_
                            p = in36_
                            next = in37_
                            raise _dafny.TailCall()
                    elif True:
                        in38_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in39_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_649_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in40_ = (next) + (1)
                        s = in38_
                        p = in39_
                        next = in40_
                        raise _dafny.TailCall()
                break

