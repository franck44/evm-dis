import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Int
import EVMOpcodes
import OpcodeDecoder
import MiscTypes
import Hex

# Module: BinaryDecoder

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Disassemble(s, p):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif (len(s)) == (1):
                    return (p) + (_dafny.SeqWithoutIsStrInference([EVMOpcodes.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMOpcodes.default__.INVALID), _dafny.SeqWithoutIsStrInference([]))]))
                elif True:
                    source4_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source4_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([EVMOpcodes.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMOpcodes.default__.INVALID), _dafny.SeqWithoutIsStrInference([]))]))
                    elif True:
                        d_8___mcc_h0_ = source4_.v
                        d_9_v_ = d_8___mcc_h0_
                        d_10_op_ = OpcodeDecoder.default__.Decode(d_9_v_)
                        if ((d_10_op_).Args()) > (0):
                            if (len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_10_op_).Args())):
                                return (p) + (_dafny.SeqWithoutIsStrInference([EVMOpcodes.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMOpcodes.default__.INVALID), _dafny.SeqWithoutIsStrInference([]))]))
                            elif True:
                                in0_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_10_op_).Args())::])
                                in1_ = (p) + (_dafny.SeqWithoutIsStrInference([EVMOpcodes.Instruction_Instruction(d_10_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_10_op_).Args()):]))]))
                                s = in0_
                                p = in1_
                                raise _dafny.TailCall()
                        elif True:
                            in2_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in3_ = (p) + (_dafny.SeqWithoutIsStrInference([EVMOpcodes.Instruction_Instruction(d_10_op_, _dafny.SeqWithoutIsStrInference([]))]))
                            s = in2_
                            p = in3_
                            raise _dafny.TailCall()
                break


class Option:
    @classmethod
    def default(cls, ):
        return lambda: Option_None()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_None(self) -> bool:
        return isinstance(self, Option_None)
    @property
    def is_Some(self) -> bool:
        return isinstance(self, Option_Some)

class Option_None(Option, NamedTuple('None_', [])):
    def __dafnystr__(self) -> str:
        return f'BinaryDecoder.Option.None'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_None)
    def __hash__(self) -> int:
        return super().__hash__()

class Option_Some(Option, NamedTuple('Some', [('v', Any)])):
    def __dafnystr__(self) -> str:
        return f'BinaryDecoder.Option.Some({_dafny.string_of(self.v)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_Some) and self.v == __o.v
    def __hash__(self) -> int:
        return super().__hash__()

