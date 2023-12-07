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
                    return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), s, next)]))
                elif True:
                    source42_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source42_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference((s)[:2:]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "' is not a known opcode"))), next)]))
                    elif True:
                        d_639___mcc_h0_ = source42_.v
                        d_640_v_ = d_639___mcc_h0_
                        d_641_op_ = OpcodeDecoder.default__.Decode(d_640_v_)
                        if ((d_641_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_641_op_).Args()))) or (not(Hex.default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_641_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_641_op_).name), next)]))
                            elif True:
                                in27_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_641_op_).Args())::])
                                in28_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_641_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_641_op_).Args()):]), next)]))
                                in29_ = ((next) + (1)) + ((d_641_op_).Args())
                                s = in27_
                                p = in28_
                                next = in29_
                                raise _dafny.TailCall()
                        elif True:
                            in30_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in31_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_641_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in32_ = (next) + (1)
                            s = in30_
                            p = in31_
                            next = in32_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_642_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_642_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_642_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), 0)]))
                        elif True:
                            in33_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_642_op_).Args()::])
                            in34_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_642_op_, Hex.default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_642_op_).Args():])), next)]))
                            in35_ = ((next) + (1)) + ((d_642_op_).Args())
                            s = in33_
                            p = in34_
                            next = in35_
                            raise _dafny.TailCall()
                    elif True:
                        in36_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in37_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_642_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in38_ = (next) + (1)
                        s = in36_
                        p = in37_
                        next = in38_
                        raise _dafny.TailCall()
                break

