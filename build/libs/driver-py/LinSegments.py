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
        d_485___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_485___accumulator_)
                elif True:
                    d_485___accumulator_ = (d_485___accumulator_) + (((xs)[0]).StackEffect())
                    in34_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in34_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreOperandsHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_486_lastI_ = (xs)[(len(xs)) - (1)]
                    d_487_e_ = (d_486_lastI_).WeakestPreOperands(postCond)
                    in35_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in36_ = d_487_e_
                    xs = in35_
                    postCond = in36_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreCapacityHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_488_lastI_ = (xs)[(len(xs)) - (1)]
                    d_489_e_ = (d_488_lastI_).WeakestPreCapacity(postCond)
                    in37_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in38_ = d_489_e_
                    xs = in37_
                    postCond = in38_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def RunIns(xs, s):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return s
                elif True:
                    d_490_next_ = ((xs)[0]).NextState(s, False)
                    source43_ = d_490_next_
                    if source43_.is_EState:
                        d_491___mcc_h0_ = source43_.pc
                        d_492___mcc_h1_ = source43_.stack
                        in39_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in40_ = d_490_next_
                        xs = in39_
                        s = in40_
                        raise _dafny.TailCall()
                    elif True:
                        d_493___mcc_h2_ = source43_.msg
                        return d_490_next_
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
                    d_494_c1_ = ((xs)[(len(xs)) - (1)]).WPre(c)
                    in41_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in42_ = d_494_c1_
                    xs = in41_
                    c = in42_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WPreSeqSegs(path, exits, c, xs, tgtPC):
        while True:
            with _dafny.label():
                if (len(path)) == (0):
                    return c
                elif True:
                    d_495_w1_ = ((xs)[(path)[(len(path)) - (1)]]).WPre(c)
                    d_496_wp2_ = ((xs)[(path)[(len(path)) - (1)]]).LeadsTo(tgtPC, (exits)[(len(exits)) - (1)])
                    in43_ = _dafny.SeqWithoutIsStrInference((path)[:(len(path)) - (1):])
                    in44_ = _dafny.SeqWithoutIsStrInference((exits)[:(len(exits)) - (1):])
                    in45_ = (d_495_w1_).And(d_496_wp2_)
                    in46_ = xs
                    in47_ = ((xs)[(path)[(len(path)) - (1)]]).StartAddress()
                    path = in43_
                    exits = in44_
                    c = in45_
                    xs = in46_
                    tgtPC = in47_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PCToSeg(xs, pc, rank):
        while True:
            with _dafny.label():
                if (rank) == (len(xs)):
                    return MiscTypes.Option_None()
                elif (((xs)[rank]).StartAddress()) == (pc):
                    return MiscTypes.Option_Some(rank)
                elif True:
                    in48_ = xs
                    in49_ = pc
                    in50_ = (rank) + (1)
                    xs = in48_
                    pc = in49_
                    rank = in50_
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
    @property
    def is_INVALIDSeg(self) -> bool:
        return isinstance(self, LinSeg_INVALIDSeg)
    def IsValid(self):
        source44_ = self
        if source44_.is_JUMPSeg:
            d_497___mcc_h0_ = source44_.ins
            d_498___mcc_h1_ = source44_.lastIns
            d_499___mcc_h2_ = source44_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMP)
        elif source44_.is_JUMPISeg:
            d_500___mcc_h3_ = source44_.ins
            d_501___mcc_h4_ = source44_.lastIns
            d_502___mcc_h5_ = source44_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMPI)
        elif source44_.is_RETURNSeg:
            d_503___mcc_h6_ = source44_.ins
            d_504___mcc_h7_ = source44_.lastIns
            d_505___mcc_h8_ = source44_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.RETURN)
        elif source44_.is_STOPSeg:
            d_506___mcc_h9_ = source44_.ins
            d_507___mcc_h10_ = source44_.lastIns
            d_508___mcc_h11_ = source44_.netOpEffect
            return (((((self).lastIns).op).opcode) == (EVMConstants.default__.STOP)) or (((((self).lastIns).op).opcode) == (EVMConstants.default__.REVERT))
        elif source44_.is_CONTSeg:
            d_509___mcc_h12_ = source44_.ins
            d_510___mcc_h13_ = source44_.lastIns
            d_511___mcc_h14_ = source44_.netOpEffect
            return ((((self).lastIns).op).opcode) != (EVMConstants.default__.INVALID)
        elif True:
            d_512___mcc_h15_ = source44_.ins
            d_513___mcc_h16_ = source44_.lastIns
            d_514___mcc_h17_ = source44_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.INVALID)

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
        d_515___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(rest)) == (0):
                    return (d_515___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif ((((rest)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    d_515___accumulator_ = (d_515___accumulator_) + (_dafny.SeqWithoutIsStrInference([((rest)[0]).address]))
                    in51_ = _this
                    in52_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in51_
                    
                    rest = in52_
                    raise _dafny.TailCall()
                elif True:
                    in53_ = _this
                    in54_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in53_
                    
                    rest = in54_
                    raise _dafny.TailCall()
                break

    def WeakestPreOperands(self, n):
        return default__.WeakestPreOperandsHelper((self).Ins(), n)

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), n)

    def Run(self, s, exit):
        d_516_s_k_ = default__.RunIns((self).ins, s)
        if (d_516_s_k_).is_Error:
            return d_516_s_k_
        elif True:
            return ((self).lastIns).NextState(d_516_s_k_, exit)

    def WPre(self, c):
        return default__.WPreIns((self).Ins(), c)

    def HasExit(self, b):
        source45_ = self
        if source45_.is_JUMPSeg:
            d_517___mcc_h0_ = source45_.ins
            d_518___mcc_h1_ = source45_.lastIns
            d_519___mcc_h2_ = source45_.netOpEffect
            return b
        elif source45_.is_JUMPISeg:
            d_520___mcc_h6_ = source45_.ins
            d_521___mcc_h7_ = source45_.lastIns
            d_522___mcc_h8_ = source45_.netOpEffect
            return True
        elif source45_.is_RETURNSeg:
            d_523___mcc_h12_ = source45_.ins
            d_524___mcc_h13_ = source45_.lastIns
            d_525___mcc_h14_ = source45_.netOpEffect
            return False
        elif source45_.is_STOPSeg:
            d_526___mcc_h18_ = source45_.ins
            d_527___mcc_h19_ = source45_.lastIns
            d_528___mcc_h20_ = source45_.netOpEffect
            return False
        elif source45_.is_CONTSeg:
            d_529___mcc_h24_ = source45_.ins
            d_530___mcc_h25_ = source45_.lastIns
            d_531___mcc_h26_ = source45_.netOpEffect
            return not(b)
        elif True:
            d_532___mcc_h30_ = source45_.ins
            d_533___mcc_h31_ = source45_.lastIns
            d_534___mcc_h32_ = source45_.netOpEffect
            return False

    def LeadsTo(self, k, exit):
        if (k) >= (Int.default__.TWO__256):
            return WeakPre.Cond_StFalse()
        elif True:
            source46_ = self
            if source46_.is_JUMPSeg:
                d_535___mcc_h0_ = source46_.ins
                d_536___mcc_h1_ = source46_.lastIns
                d_537___mcc_h2_ = source46_.netOpEffect
                if exit:
                    d_538_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                    return default__.WPreIns((self).ins, d_538_c_)
                elif True:
                    return WeakPre.Cond_StFalse()
            elif source46_.is_JUMPISeg:
                d_539___mcc_h3_ = source46_.ins
                d_540___mcc_h4_ = source46_.lastIns
                d_541___mcc_h5_ = source46_.netOpEffect
                if exit:
                    d_542_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                    return default__.WPreIns((self).ins, d_542_c_)
                elif (k) == ((self).StartAddressNextSeg()):
                    return WeakPre.Cond_StTrue()
                elif True:
                    return WeakPre.Cond_StFalse()
            elif source46_.is_RETURNSeg:
                d_543___mcc_h6_ = source46_.ins
                d_544___mcc_h7_ = source46_.lastIns
                d_545___mcc_h8_ = source46_.netOpEffect
                return WeakPre.Cond_StTrue()
            elif source46_.is_STOPSeg:
                d_546___mcc_h9_ = source46_.ins
                d_547___mcc_h10_ = source46_.lastIns
                d_548___mcc_h11_ = source46_.netOpEffect
                return WeakPre.Cond_StTrue()
            elif source46_.is_CONTSeg:
                d_549___mcc_h12_ = source46_.ins
                d_550___mcc_h13_ = source46_.lastIns
                d_551___mcc_h14_ = source46_.netOpEffect
                if (not(exit)) and ((k) == ((self).StartAddressNextSeg())):
                    return WeakPre.Cond_StTrue()
                elif True:
                    return WeakPre.Cond_StFalse()
            elif True:
                d_552___mcc_h15_ = source46_.ins
                d_553___mcc_h16_ = source46_.lastIns
                d_554___mcc_h17_ = source46_.netOpEffect
                return WeakPre.Cond_StFalse()


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

class LinSeg_INVALIDSeg(LinSeg, NamedTuple('INVALIDSeg', [('ins', Any), ('lastIns', Any), ('netOpEffect', Any)])):
    def __dafnystr__(self) -> str:
        return f'LinSegments.LinSeg.INVALIDSeg({_dafny.string_of(self.ins)}, {_dafny.string_of(self.lastIns)}, {_dafny.string_of(self.netOpEffect)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LinSeg_INVALIDSeg) and self.ins == __o.ins and self.lastIns == __o.lastIns and self.netOpEffect == __o.netOpEffect
    def __hash__(self) -> int:
        return super().__hash__()

