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
                    return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), next)]))
                elif True:
                    source5_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source5_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), next)]))
                    elif True:
                        d_82___mcc_h0_ = source5_.v
                        d_83_v_ = d_82___mcc_h0_
                        d_84_op_ = OpcodeDecoder.default__.Decode(d_83_v_)
                        if ((d_84_op_).Args()) > (0):
                            if (len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_84_op_).Args())):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), 0)]))
                            elif True:
                                in0_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_84_op_).Args())::])
                                in1_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_84_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_84_op_).Args()):]), next)]))
                                in2_ = ((next) + (1)) + ((d_84_op_).Args())
                                s = in0_
                                p = in1_
                                next = in2_
                                raise _dafny.TailCall()
                        elif True:
                            in3_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in4_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_84_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in5_ = (next) + (1)
                            s = in3_
                            p = in4_
                            next = in5_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_85_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_85_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_85_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), 0)]))
                        elif True:
                            in6_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_85_op_).Args()::])
                            in7_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_85_op_, default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_85_op_).Args():])), next)]))
                            in8_ = ((next) + (1)) + ((d_85_op_).Args())
                            s = in6_
                            p = in7_
                            next = in8_
                            raise _dafny.TailCall()
                    elif True:
                        in9_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in10_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_85_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in11_ = (next) + (1)
                        s = in9_
                        p = in10_
                        next = in11_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def HexHelper(s):
        d_86___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_86___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_86___accumulator_ = (d_86___accumulator_) + (Hex.default__.U8ToHex((s)[0]))
                    in12_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in12_
                    raise _dafny.TailCall()
                break

