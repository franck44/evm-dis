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
        d_467___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_467___accumulator_)
                elif True:
                    d_467___accumulator_ = (d_467___accumulator_) + (((xs)[0]).StackEffect())
                    in27_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in27_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreOperandsHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_468_lastI_ = (xs)[(len(xs)) - (1)]
                    d_469_e_ = (d_468_lastI_).WeakestPreOperands(postCond)
                    in28_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in29_ = d_469_e_
                    xs = in28_
                    postCond = in29_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreCapacityHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_470_lastI_ = (xs)[(len(xs)) - (1)]
                    d_471_e_ = (d_470_lastI_).WeakestPreCapacity(postCond)
                    in30_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in31_ = d_471_e_
                    xs = in30_
                    postCond = in31_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def RunIns(xs, s):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return s
                elif True:
                    d_472_next_ = ((xs)[0]).NextState(s, False)
                    source38_ = d_472_next_
                    if source38_.is_EState:
                        d_473___mcc_h0_ = source38_.pc
                        d_474___mcc_h1_ = source38_.stack
                        in32_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in33_ = d_472_next_
                        xs = in32_
                        s = in33_
                        raise _dafny.TailCall()
                    elif True:
                        d_475___mcc_h2_ = source38_.msg
                        return d_472_next_
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
                    d_476_c1_ = ((xs)[(len(xs)) - (1)]).WPre(c)
                    in34_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in35_ = d_476_c1_
                    xs = in34_
                    c = in35_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WPreSeqSegs(path, c, xs):
        while True:
            with _dafny.label():
                if (not((c).is_StCond)) or ((len(path)) == (0)):
                    return c
                elif True:
                    d_477_w1_ = ((xs)[(path)[(len(path)) - (1)]]).WPre(c)
                    in36_ = _dafny.SeqWithoutIsStrInference((path)[:(len(path)) - (1):])
                    in37_ = d_477_w1_
                    in38_ = xs
                    path = in36_
                    c = in37_
                    xs = in38_
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
        source39_ = self
        if source39_.is_JUMPSeg:
            d_478___mcc_h0_ = source39_.ins
            d_479___mcc_h1_ = source39_.lastIns
            d_480___mcc_h2_ = source39_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMP)
        elif source39_.is_JUMPISeg:
            d_481___mcc_h3_ = source39_.ins
            d_482___mcc_h4_ = source39_.lastIns
            d_483___mcc_h5_ = source39_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMPI)
        elif source39_.is_RETURNSeg:
            d_484___mcc_h6_ = source39_.ins
            d_485___mcc_h7_ = source39_.lastIns
            d_486___mcc_h8_ = source39_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.RETURN)
        elif source39_.is_STOPSeg:
            d_487___mcc_h9_ = source39_.ins
            d_488___mcc_h10_ = source39_.lastIns
            d_489___mcc_h11_ = source39_.netOpEffect
            return (((((self).lastIns).op).opcode) == (EVMConstants.default__.STOP)) or (((((self).lastIns).op).opcode) == (EVMConstants.default__.REVERT))
        elif True:
            d_490___mcc_h12_ = source39_.ins
            d_491___mcc_h13_ = source39_.lastIns
            d_492___mcc_h14_ = source39_.netOpEffect
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
        d_493___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(rest)) == (0):
                    return (d_493___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif ((((rest)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    d_493___accumulator_ = (d_493___accumulator_) + (_dafny.SeqWithoutIsStrInference([((rest)[0]).address]))
                    in39_ = _this
                    in40_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in39_
                    
                    rest = in40_
                    raise _dafny.TailCall()
                elif True:
                    in41_ = _this
                    in42_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in41_
                    
                    rest = in42_
                    raise _dafny.TailCall()
                break

    def WeakestPreOperands(self, n):
        return default__.WeakestPreOperandsHelper((self).Ins(), n)

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), n)

    def Run(self, s, exit):
        d_494_s_k_ = default__.RunIns((self).ins, s)
        if (d_494_s_k_).is_Error:
            return d_494_s_k_
        elif True:
            return ((self).lastIns).NextState(d_494_s_k_, exit)

    def WPre(self, c):
        return default__.WPreIns((self).Ins(), c)

    def HasExit(self, b):
        source40_ = self
        if source40_.is_JUMPSeg:
            d_495___mcc_h0_ = source40_.ins
            d_496___mcc_h1_ = source40_.lastIns
            d_497___mcc_h2_ = source40_.netOpEffect
            return b
        elif source40_.is_JUMPISeg:
            d_498___mcc_h6_ = source40_.ins
            d_499___mcc_h7_ = source40_.lastIns
            d_500___mcc_h8_ = source40_.netOpEffect
            return True
        elif source40_.is_RETURNSeg:
            d_501___mcc_h12_ = source40_.ins
            d_502___mcc_h13_ = source40_.lastIns
            d_503___mcc_h14_ = source40_.netOpEffect
            return False
        elif source40_.is_STOPSeg:
            d_504___mcc_h18_ = source40_.ins
            d_505___mcc_h19_ = source40_.lastIns
            d_506___mcc_h20_ = source40_.netOpEffect
            return False
        elif True:
            d_507___mcc_h24_ = source40_.ins
            d_508___mcc_h25_ = source40_.lastIns
            d_509___mcc_h26_ = source40_.netOpEffect
            return not(b)

    def LeadsTo(self, k):
        d_510_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
        return default__.WPreIns((self).ins, d_510_c_)


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

