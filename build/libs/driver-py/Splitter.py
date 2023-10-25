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

# Module: Splitter

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildSeg(xs, lastInst):
        if (((lastInst).op).opcode) == (86):
            return LinSeg_JUMPSeg(xs, lastInst)
        elif (((lastInst).op).opcode) == (87):
            return LinSeg_JUMPISeg(xs, lastInst)
        elif (((lastInst).op).opcode) == (243):
            return LinSeg_RETURNSeg(xs, lastInst)
        elif (((lastInst).op).opcode) == (0):
            return LinSeg_STOPSeg(xs, lastInst)
        elif True:
            return LinSeg_UNKNOWNSeg(xs, lastInst)

    @staticmethod
    def SplitUpToTerminal(xs, curseq, collected):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return collected
                elif ((xs)[0]).IsTerminal():
                    d_87_newSeg_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in13_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in14_ = _dafny.SeqWithoutIsStrInference([])
                    in15_ = (collected) + (_dafny.SeqWithoutIsStrInference([default__.BuildSeg(curseq, (xs)[0])]))
                    xs = in13_
                    curseq = in14_
                    collected = in15_
                    raise _dafny.TailCall()
                elif True:
                    in16_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in17_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in18_ = collected
                    xs = in16_
                    curseq = in17_
                    collected = in18_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreOperandsHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return MiscTypes.Option_Some(postCond)
                elif True:
                    d_88_lastI_ = (xs)[(len(xs)) - (1)]
                    d_89_e_ = (d_88_lastI_).WeakestPreOperands(postCond)
                    if (d_89_e_) >= (0):
                        in19_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in20_ = d_89_e_
                        xs = in19_
                        postCond = in20_
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
                    d_90_lastI_ = (xs)[(len(xs)) - (1)]
                    d_91_e_ = (d_90_lastI_).WeakestPreCapacity(postCond)
                    if (d_91_e_) >= (0):
                        in21_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in22_ = d_91_e_
                        xs = in21_
                        postCond = in22_
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

    def WeakestPreOperands(self, n):
        return default__.WeakestPreOperandsHelper((self).Ins(), 0)

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), 0)


class LinSeg_JUMPSeg(LinSeg, NamedTuple('JUMPSeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'Splitter.LinSeg.JUMPSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_JUMPSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_JUMPISeg(LinSeg, NamedTuple('JUMPISeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'Splitter.LinSeg.JUMPISeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_JUMPISeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_RETURNSeg(LinSeg, NamedTuple('RETURNSeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'Splitter.LinSeg.RETURNSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_RETURNSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_STOPSeg(LinSeg, NamedTuple('STOPSeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'Splitter.LinSeg.STOPSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_STOPSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_UNKNOWNSeg(LinSeg, NamedTuple('UNKNOWNSeg', [('ins', Any), ('lastIns', Any)])):
    def __dafnystr__(self) -> str:
        return f'Splitter.LinSeg.UNKNOWNSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_UNKNOWNSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns
    def __hash__(self) -> int:
        return super().__hash__()

