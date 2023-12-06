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
import WeakPre
import State
import EVMToolTips
import Instructions
import BinaryDecoder

# Module: LinSegments

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def StackEffectHelper(xs):
        d_644___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_644___accumulator_)
                elif True:
                    d_644___accumulator_ = (d_644___accumulator_) + (((xs)[0]).StackEffect())
                    in40_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in40_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreOperandsHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_645_lastI_ = (xs)[(len(xs)) - (1)]
                    d_646_e_ = (d_645_lastI_).WeakestPreOperands(postCond)
                    in41_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in42_ = d_646_e_
                    xs = in41_
                    postCond = in42_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreCapacityHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_647_lastI_ = (xs)[(len(xs)) - (1)]
                    d_648_e_ = (d_647_lastI_).WeakestPreCapacity(postCond)
                    in43_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in44_ = d_648_e_
                    xs = in43_
                    postCond = in44_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def RunIns(xs, s, jumpDests):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return s
                elif True:
                    d_649_next_ = ((xs)[0]).NextState(s, jumpDests, False)
                    source44_ = d_649_next_
                    if source44_.is_EState:
                        d_650___mcc_h0_ = source44_.pc
                        d_651___mcc_h1_ = source44_.stack
                        in45_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in46_ = d_649_next_
                        in47_ = jumpDests
                        xs = in45_
                        s = in46_
                        jumpDests = in47_
                        raise _dafny.TailCall()
                    elif True:
                        d_652___mcc_h2_ = source44_.msg
                        return d_649_next_
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
                    d_653_c1_ = ((xs)[(len(xs)) - (1)]).WPre(c)
                    in48_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in49_ = d_653_c1_
                    xs = in48_
                    c = in49_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WPreSeqSegs(path, exits, c, xs, tgtPC):
        while True:
            with _dafny.label():
                if (len(path)) == (0):
                    return c
                elif True:
                    d_654_w1_ = ((xs)[(path)[(len(path)) - (1)]]).WPre(c)
                    d_655_wp2_ = ((xs)[(path)[(len(path)) - (1)]]).LeadsTo(tgtPC, (exits)[(len(exits)) - (1)])
                    in50_ = _dafny.SeqWithoutIsStrInference((path)[:(len(path)) - (1):])
                    in51_ = _dafny.SeqWithoutIsStrInference((exits)[:(len(exits)) - (1):])
                    in52_ = (d_654_w1_).And(d_655_wp2_)
                    in53_ = xs
                    in54_ = ((xs)[(path)[(len(path)) - (1)]]).StartAddress()
                    path = in50_
                    exits = in51_
                    c = in52_
                    xs = in53_
                    tgtPC = in54_
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
                    in55_ = xs
                    in56_ = pc
                    in57_ = (rank) + (1)
                    xs = in55_
                    pc = in56_
                    rank = in57_
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
        source45_ = self
        if source45_.is_JUMPSeg:
            d_656___mcc_h0_ = source45_.ins
            d_657___mcc_h1_ = source45_.lastIns
            d_658___mcc_h2_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMP)
        elif source45_.is_JUMPISeg:
            d_659___mcc_h3_ = source45_.ins
            d_660___mcc_h4_ = source45_.lastIns
            d_661___mcc_h5_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMPI)
        elif source45_.is_RETURNSeg:
            d_662___mcc_h6_ = source45_.ins
            d_663___mcc_h7_ = source45_.lastIns
            d_664___mcc_h8_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.RETURN)
        elif source45_.is_STOPSeg:
            d_665___mcc_h9_ = source45_.ins
            d_666___mcc_h10_ = source45_.lastIns
            d_667___mcc_h11_ = source45_.netOpEffect
            return (((((self).lastIns).op).opcode) == (EVMConstants.default__.STOP)) or (((((self).lastIns).op).opcode) == (EVMConstants.default__.REVERT))
        elif source45_.is_CONTSeg:
            d_668___mcc_h12_ = source45_.ins
            d_669___mcc_h13_ = source45_.lastIns
            d_670___mcc_h14_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) != (EVMConstants.default__.INVALID)
        elif True:
            d_671___mcc_h15_ = source45_.ins
            d_672___mcc_h16_ = source45_.lastIns
            d_673___mcc_h17_ = source45_.netOpEffect
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
        d_674___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(rest)) == (0):
                    return (d_674___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif ((((rest)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    d_674___accumulator_ = (d_674___accumulator_) + (_dafny.SeqWithoutIsStrInference([((rest)[0]).address]))
                    in58_ = _this
                    in59_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in58_
                    
                    rest = in59_
                    raise _dafny.TailCall()
                elif True:
                    in60_ = _this
                    in61_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in60_
                    
                    rest = in61_
                    raise _dafny.TailCall()
                break

    def WeakestPreOperands(self, n):
        return default__.WeakestPreOperandsHelper((self).Ins(), n)

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), n)

    def Run(self, s, exit, jumpDests):
        d_675_s_k_ = default__.RunIns((self).ins, s, jumpDests)
        if (d_675_s_k_).is_Error:
            return d_675_s_k_
        elif True:
            return ((self).lastIns).NextState(d_675_s_k_, jumpDests, exit)

    def WPre(self, c):
        return default__.WPreIns((self).Ins(), c)

    def HasExit(self, b):
        source46_ = self
        if source46_.is_JUMPSeg:
            d_676___mcc_h0_ = source46_.ins
            d_677___mcc_h1_ = source46_.lastIns
            d_678___mcc_h2_ = source46_.netOpEffect
            return b
        elif source46_.is_JUMPISeg:
            d_679___mcc_h6_ = source46_.ins
            d_680___mcc_h7_ = source46_.lastIns
            d_681___mcc_h8_ = source46_.netOpEffect
            return True
        elif source46_.is_RETURNSeg:
            d_682___mcc_h12_ = source46_.ins
            d_683___mcc_h13_ = source46_.lastIns
            d_684___mcc_h14_ = source46_.netOpEffect
            return False
        elif source46_.is_STOPSeg:
            d_685___mcc_h18_ = source46_.ins
            d_686___mcc_h19_ = source46_.lastIns
            d_687___mcc_h20_ = source46_.netOpEffect
            return False
        elif source46_.is_CONTSeg:
            d_688___mcc_h24_ = source46_.ins
            d_689___mcc_h25_ = source46_.lastIns
            d_690___mcc_h26_ = source46_.netOpEffect
            return not(b)
        elif True:
            d_691___mcc_h30_ = source46_.ins
            d_692___mcc_h31_ = source46_.lastIns
            d_693___mcc_h32_ = source46_.netOpEffect
            return False

    def LeadsTo(self, k, exit):
        if (k) >= (Int.default__.TWO__256):
            return WeakPre.Cond_StFalse()
        elif True:
            source47_ = self
            if source47_.is_JUMPSeg:
                d_694___mcc_h0_ = source47_.ins
                d_695___mcc_h1_ = source47_.lastIns
                d_696___mcc_h2_ = source47_.netOpEffect
                if exit:
                    d_697_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                    return default__.WPreIns((self).ins, d_697_c_)
                elif True:
                    return WeakPre.Cond_StFalse()
            elif source47_.is_JUMPISeg:
                d_698___mcc_h3_ = source47_.ins
                d_699___mcc_h4_ = source47_.lastIns
                d_700___mcc_h5_ = source47_.netOpEffect
                if exit:
                    d_701_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                    return default__.WPreIns((self).ins, d_701_c_)
                elif (k) == ((self).StartAddressNextSeg()):
                    return WeakPre.Cond_StTrue()
                elif True:
                    return WeakPre.Cond_StFalse()
            elif source47_.is_RETURNSeg:
                d_702___mcc_h6_ = source47_.ins
                d_703___mcc_h7_ = source47_.lastIns
                d_704___mcc_h8_ = source47_.netOpEffect
                return WeakPre.Cond_StTrue()
            elif source47_.is_STOPSeg:
                d_705___mcc_h9_ = source47_.ins
                d_706___mcc_h10_ = source47_.lastIns
                d_707___mcc_h11_ = source47_.netOpEffect
                return WeakPre.Cond_StTrue()
            elif source47_.is_CONTSeg:
                d_708___mcc_h12_ = source47_.ins
                d_709___mcc_h13_ = source47_.lastIns
                d_710___mcc_h14_ = source47_.netOpEffect
                if (not(exit)) and ((k) == ((self).StartAddressNextSeg())):
                    return WeakPre.Cond_StTrue()
                elif True:
                    return WeakPre.Cond_StFalse()
            elif True:
                d_711___mcc_h15_ = source47_.ins
                d_712___mcc_h16_ = source47_.lastIns
                d_713___mcc_h17_ = source47_.netOpEffect
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

