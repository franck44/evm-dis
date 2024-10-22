import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import MiscTypes as MiscTypes
import Int as Int
import EVMConstants as EVMConstants
import EVMOpcodes as EVMOpcodes
import OpcodeDecoder as OpcodeDecoder
import Hex as Hex
import StackElement as StackElement
import WeakPre as WeakPre
import State as State
import EVMToolTips as EVMToolTips
import Instructions as Instructions

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
                    source0_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if True:
                        if source0_.is_None:
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference((s)[:2:]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "' is not an Hex number"))), next)]))
                    if True:
                        d_0_v_ = source0_.v
                        d_1_op_ = OpcodeDecoder.default__.Decode(d_0_v_)
                        if ((d_1_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_1_op_).Args()))) or (not(Hex.default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_1_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_1_op_).name), next)]))
                            elif True:
                                in0_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_1_op_).Args())::])
                                in1_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_1_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_1_op_).Args()):]), next)]))
                                in2_ = ((next) + (1)) + ((d_1_op_).Args())
                                s = in0_
                                p = in1_
                                next = in2_
                                raise _dafny.TailCall()
                        elif True:
                            in3_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in4_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_1_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
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
                    d_0_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_0_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_0_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for opcode "))) + ((d_0_op_).name), next)]))
                        elif True:
                            in0_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_0_op_).Args()::])
                            in1_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_0_op_, Hex.default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_0_op_).Args():])), next)]))
                            in2_ = ((next) + (1)) + ((d_0_op_).Args())
                            s = in0_
                            p = in1_
                            next = in2_
                            raise _dafny.TailCall()
                    elif True:
                        in3_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in4_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_0_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in5_ = (next) + (1)
                        s = in3_
                        p = in4_
                        next = in5_
                        raise _dafny.TailCall()
                break

