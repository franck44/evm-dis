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
import BinaryDecoder

# Module: LinSegments

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def WeakestPreOperandsHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return MiscTypes.Option_Some(postCond)
                elif True:
                    d_172_lastI_ = (xs)[(len(xs)) - (1)]
                    d_173_e_ = (d_172_lastI_).WeakestPreOperands(postCond)
                    if (d_173_e_) >= (0):
                        in14_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in15_ = d_173_e_
                        xs = in14_
                        postCond = in15_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def WeakestPreCapacityHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return MiscTypes.Option_Some(postCond)
                elif True:
                    d_174_lastI_ = (xs)[(len(xs)) - (1)]
                    d_175_e_ = (d_174_lastI_).WeakestPreCapacity(postCond)
                    if (d_175_e_) >= (0):
                        in16_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in17_ = d_175_e_
                        xs = in16_
                        postCond = in17_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break


class LinSeg:
    @classmethod
    def default(cls, ):
        return lambda: LinSeg_JUMPSeg(_dafny.Seq({}), Instructions.Instruction.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_JUMPSeg(self) -> bool:
        return isinstance(self, LinSeg_JUMPSeg)
    @property
    def is_JUMPISeg(self) -> bool:
        return isinstance(self, LinSeg_JUMPISeg)
    @property
    def is_RETURNSeg(self) -> bool:
        return isinstance(self, LinSeg_RETURNSeg)
    @property
    def is_STOPSeg(self) -> bool:
        return isinstance(self, LinSeg_STOPSeg)
    @property
    def is_UNKNOWNSeg(self) -> bool:
        return isinstance(self, LinSeg_UNKNOWNSeg)
    def Ins(self):
        return ((self).ins) + (_dafny.SeqWithoutIsStrInference([(self).lastIns]))

    def CollectJumpDest(self, rest):
        d_176___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(rest)) == (0):
                    return (d_176___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif ((((rest)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    d_176___accumulator_ = (d_176___accumulator_) + (_dafny.SeqWithoutIsStrInference([((rest)[0]).address]))
                    in18_ = _this
                    in19_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in18_
                    
                    rest = in19_
                    raise _dafny.TailCall()
                elif True:
                    in20_ = _this
                    in21_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in20_
                    
                    rest = in21_
                    raise _dafny.TailCall()
                break

    def WeakestPreOperands(self, n):
        return default__.WeakestPreOperandsHelper((self).Ins(), 0)

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), 0)


class LinSeg_JUMPSeg(LinSeg, NamedTuple('JUMPSeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.JUMPSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_JUMPSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_JUMPISeg(LinSeg, NamedTuple('JUMPISeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.JUMPISeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_JUMPISeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_RETURNSeg(LinSeg, NamedTuple('RETURNSeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.RETURNSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_RETURNSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_STOPSeg(LinSeg, NamedTuple('STOPSeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.STOPSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_STOPSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_UNKNOWNSeg(LinSeg, NamedTuple('UNKNOWNSeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.UNKNOWNSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_UNKNOWNSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

