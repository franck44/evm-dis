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
import OpcodeDecoder
import Hex
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
                    source6_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source6_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference((s)[:2:]), next)]))
                    elif True:
                        d_167___mcc_h0_ = source6_.v
                        d_168_v_ = d_167___mcc_h0_
                        d_169_op_ = OpcodeDecoder.default__.Decode(d_168_v_)
                        if ((d_169_op_).Args()) > (0):
                            if (len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_169_op_).Args())):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for "))) + (_dafny.SeqWithoutIsStrInference((s)[2::])), next)]))
                            elif True:
                                in1_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_169_op_).Args())::])
                                in2_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_169_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_169_op_).Args()):]), next)]))
                                in3_ = ((next) + (1)) + ((d_169_op_).Args())
                                s = in1_
                                p = in2_
                                next = in3_
                                raise _dafny.TailCall()
                        elif True:
                            in4_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in5_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_169_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in6_ = (next) + (1)
                            s = in4_
                            p = in5_
                            next = in6_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_170_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_170_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_170_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), 0)]))
                        elif True:
                            in7_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_170_op_).Args()::])
                            in8_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_170_op_, default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_170_op_).Args():])), next)]))
                            in9_ = ((next) + (1)) + ((d_170_op_).Args())
                            s = in7_
                            p = in8_
                            next = in9_
                            raise _dafny.TailCall()
                    elif True:
                        in10_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in11_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_170_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in12_ = (next) + (1)
                        s = in10_
                        p = in11_
                        next = in12_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def HexHelper(s):
        d_171___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_171___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_171___accumulator_ = (d_171___accumulator_) + (Hex.default__.U8ToHex((s)[0]))
                    in13_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in13_
                    raise _dafny.TailCall()
                break

