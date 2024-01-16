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
                    source43_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source43_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference((s)[:2:]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "' is not an Hex number"))), next)]))
                    elif True:
                        d_652___mcc_h0_ = source43_.v
                        d_653_v_ = d_652___mcc_h0_
                        d_654_op_ = OpcodeDecoder.default__.Decode(d_653_v_)
                        if ((d_654_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_654_op_).Args()))) or (not(Hex.default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_654_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_654_op_).name), next)]))
                            elif True:
                                in39_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_654_op_).Args())::])
                                in40_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_654_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_654_op_).Args()):]), next)]))
                                in41_ = ((next) + (1)) + ((d_654_op_).Args())
                                s = in39_
                                p = in40_
                                next = in41_
                                raise _dafny.TailCall()
                        elif True:
                            in42_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in43_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_654_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in44_ = (next) + (1)
                            s = in42_
                            p = in43_
                            next = in44_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_655_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_655_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_655_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_655_op_).name), next)]))
                        elif True:
                            in45_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_655_op_).Args()::])
                            in46_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_655_op_, Hex.default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_655_op_).Args():])), next)]))
                            in47_ = ((next) + (1)) + ((d_655_op_).Args())
                            s = in45_
                            p = in46_
                            next = in47_
                            raise _dafny.TailCall()
                    elif True:
                        in48_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in49_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_655_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in50_ = (next) + (1)
                        s = in48_
                        p = in49_
                        next = in50_
                        raise _dafny.TailCall()
                break

