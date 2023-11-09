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
import StackElement
import State
import WeakPre
import Instructions
import BinaryDecoder

# Module: LinSegments

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def StackEffectHelper(xs):
        d_457___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_457___accumulator_)
                elif True:
                    d_457___accumulator_ = (d_457___accumulator_) + (((xs)[0]).StackEffect())
                    in26_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in26_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreOperandsHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_458_lastI_ = (xs)[(len(xs)) - (1)]
                    d_459_e_ = (d_458_lastI_).WeakestPreOperands(postCond)
                    in27_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in28_ = d_459_e_
                    xs = in27_
                    postCond = in28_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreCapacityHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_460_lastI_ = (xs)[(len(xs)) - (1)]
                    d_461_e_ = (d_460_lastI_).WeakestPreCapacity(postCond)
                    in29_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in30_ = d_461_e_
                    xs = in29_
                    postCond = in30_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def RunIns(xs, s):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return s
                elif True:
                    d_462_next_ = ((xs)[0]).NextState(s, False)
                    source36_ = d_462_next_
                    if source36_.is_EState:
                        d_463___mcc_h0_ = source36_.pc
                        d_464___mcc_h1_ = source36_.stack
                        in31_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in32_ = d_462_next_
                        xs = in31_
                        s = in32_
                        raise _dafny.TailCall()
                    elif True:
                        d_465___mcc_h2_ = source36_.msg
                        return d_462_next_
                break

    @staticmethod
    def WPreIns(xs, c):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return c
                elif not((c).is_StCond):
                    return c
                elif True:
                    d_466_c1_ = ((xs)[(len(xs)) - (1)]).WPre(c)
                    in33_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in34_ = d_466_c1_
                    xs = in33_
                    c = in34_
                    raise _dafny.TailCall()
                break


class ValidLinSeg:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return LinSeg_CONTSeg(_dafny.SeqWithoutIsStrInference([]), Instructions.Instruction_Instruction(EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ADD")), EVMConstants.default__.ADD, 0, 2, 1, 2), _dafny.SeqWithoutIsStrInference([]), 0), 0)

class LinSeg:
    @classmethod
    def default(cls, ):
        return lambda: LinSeg_JUMPSeg(_dafny.Seq({}), Instructions.ValidInstruction.default(), int(0))
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
    def is_CONTSeg(self) -> bool:
        return isinstance(self, LinSeg_CONTSeg)
    def IsValid(self):
        source37_ = self
        if source37_.is_JUMPSeg:
            d_467___mcc_h0_ = source37_.ins
            d_468___mcc_h1_ = source37_.lastIns
            d_469___mcc_h2_ = source37_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMP)
        elif source37_.is_JUMPISeg:
            d_470___mcc_h3_ = source37_.ins
            d_471___mcc_h4_ = source37_.lastIns
            d_472___mcc_h5_ = source37_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMPI)
        elif source37_.is_RETURNSeg:
            d_473___mcc_h6_ = source37_.ins
            d_474___mcc_h7_ = source37_.lastIns
            d_475___mcc_h8_ = source37_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.RETURN)
        elif source37_.is_STOPSeg:
            d_476___mcc_h9_ = source37_.ins
            d_477___mcc_h10_ = source37_.lastIns
            d_478___mcc_h11_ = source37_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.STOP)
        elif True:
            d_479___mcc_h12_ = source37_.ins
            d_480___mcc_h13_ = source37_.lastIns
            d_481___mcc_h14_ = source37_.netOpEffect
            return True

    def Ins(self):
        return ((self).ins) + (_dafny.SeqWithoutIsStrInference([(self).lastIns]))

    def StartAddress(self):
        return (((self).Ins())[0]).address

    def NetOpEffect(self):
        return (self).netOpEffect

    def NetCapEffect(self):
        return (0) - ((self).netOpEffect)

    def StackEffect(self):
        return (self).netOpEffect

    def StartAddressNextSeg(self):
        return ((((self).lastIns).address) + (1)) + (_dafny.euclidian_division(len(((self).lastIns).arg), 2))

    def CollectJumpDest(self, rest):
        d_482___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(rest)) == (0):
                    return (d_482___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif ((((rest)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    d_482___accumulator_ = (d_482___accumulator_) + (_dafny.SeqWithoutIsStrInference([((rest)[0]).address]))
                    in35_ = _this
                    in36_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in35_
                    
                    rest = in36_
                    raise _dafny.TailCall()
                elif True:
                    in37_ = _this
                    in38_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in37_
                    
                    rest = in38_
                    raise _dafny.TailCall()
                break

    def WeakestPreOperands(self, n):
        return default__.WeakestPreOperandsHelper((self).Ins(), n)

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), n)

    def Run(self, s, exit):
        d_483_s_k_ = default__.RunIns((self).ins, s)
        if (d_483_s_k_).is_Error:
            return d_483_s_k_
        elif True:
            return ((self).lastIns).NextState(d_483_s_k_, exit)

    def WPre(self, c):
        return default__.WPreIns((self).Ins(), c)

    def HasExit(self, b):
        source38_ = self
        if source38_.is_JUMPSeg:
            d_484___mcc_h0_ = source38_.ins
            d_485___mcc_h1_ = source38_.lastIns
            d_486___mcc_h2_ = source38_.netOpEffect
            return b
        elif source38_.is_JUMPISeg:
            d_487___mcc_h6_ = source38_.ins
            d_488___mcc_h7_ = source38_.lastIns
            d_489___mcc_h8_ = source38_.netOpEffect
            return True
        elif source38_.is_RETURNSeg:
            d_490___mcc_h12_ = source38_.ins
            d_491___mcc_h13_ = source38_.lastIns
            d_492___mcc_h14_ = source38_.netOpEffect
            return False
        elif source38_.is_STOPSeg:
            d_493___mcc_h18_ = source38_.ins
            d_494___mcc_h19_ = source38_.lastIns
            d_495___mcc_h20_ = source38_.netOpEffect
            return False
        elif True:
            d_496___mcc_h24_ = source38_.ins
            d_497___mcc_h25_ = source38_.lastIns
            d_498___mcc_h26_ = source38_.netOpEffect
            return not(b)


class LinSeg_JUMPSeg(LinSeg, NamedTuple('JUMPSeg', [('ins', Any), ('lastIns', Any), ('netOpEffect', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.JUMPSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)}, {_dafny.string_of(self.netOpEffect)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_JUMPSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns and self.netOpEffect == __o.netOpEffect
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_JUMPISeg(LinSeg, NamedTuple('JUMPISeg', [('ins', Any), ('lastIns', Any), ('netOpEffect', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.JUMPISeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)}, {_dafny.string_of(self.netOpEffect)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_JUMPISeg) and self.ins == __o.ins and self.lastIns == __o.lastIns and self.netOpEffect == __o.netOpEffect
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_RETURNSeg(LinSeg, NamedTuple('RETURNSeg', [('ins', Any), ('lastIns', Any), ('netOpEffect', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.RETURNSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)}, {_dafny.string_of(self.netOpEffect)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_RETURNSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns and self.netOpEffect == __o.netOpEffect
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_STOPSeg(LinSeg, NamedTuple('STOPSeg', [('ins', Any), ('lastIns', Any), ('netOpEffect', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.STOPSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)}, {_dafny.string_of(self.netOpEffect)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_STOPSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns and self.netOpEffect == __o.netOpEffect
    def __hash__(self) -> int:
        return super().__hash__()

class LinSeg_CONTSeg(LinSeg, NamedTuple('CONTSeg', [('ins', Any), ('lastIns', Any), ('netOpEffect', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.CONTSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)}, {_dafny.string_of(self.netOpEffect)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_CONTSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns and self.netOpEffect == __o.netOpEffect
    def __hash__(self) -> int:
        return super().__hash__()

