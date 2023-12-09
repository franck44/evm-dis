import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes
import Int
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
        d_643___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_643___accumulator_)
                elif True:
                    d_643___accumulator_ = (d_643___accumulator_) + (((xs)[0]).StackEffect())
                    in39_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in39_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreOperandsHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_644_lastI_ = (xs)[(len(xs)) - (1)]
                    d_645_e_ = (d_644_lastI_).WeakestPreOperands(postCond)
                    in40_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in41_ = d_645_e_
                    xs = in40_
                    postCond = in41_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreCapacityHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_646_lastI_ = (xs)[(len(xs)) - (1)]
                    d_647_e_ = (d_646_lastI_).WeakestPreCapacity(postCond)
                    in42_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in43_ = d_647_e_
                    xs = in42_
                    postCond = in43_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def RunIns(xs, s, jumpDests):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return s
                elif True:
                    d_648_next_ = ((xs)[0]).NextState(s, jumpDests, False)
                    source43_ = d_648_next_
                    if source43_.is_EState:
                        d_649___mcc_h0_ = source43_.pc
                        d_650___mcc_h1_ = source43_.stack
                        in44_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in45_ = d_648_next_
                        in46_ = jumpDests
                        xs = in44_
                        s = in45_
                        jumpDests = in46_
                        raise _dafny.TailCall()
                    elif True:
                        d_651___mcc_h2_ = source43_.msg
                        return d_648_next_
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
                    d_652_c1_ = ((xs)[(len(xs)) - (1)]).WPre(c)
                    in47_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in48_ = d_652_c1_
                    xs = in47_
                    c = in48_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WPreSeqSegs(path, exits, c, xs, tgtPC):
        while True:
            with _dafny.label():
                if (len(path)) == (0):
                    return c
                elif True:
                    d_653_w1_ = ((xs)[(path)[(len(path)) - (1)]]).WPre(c)
                    d_654_wp2_ = ((xs)[(path)[(len(path)) - (1)]]).LeadsTo(tgtPC, (exits)[(len(exits)) - (1)])
                    in49_ = _dafny.SeqWithoutIsStrInference((path)[:(len(path)) - (1):])
                    in50_ = _dafny.SeqWithoutIsStrInference((exits)[:(len(exits)) - (1):])
                    in51_ = (d_653_w1_).And(d_654_wp2_)
                    in52_ = xs
                    in53_ = ((xs)[(path)[(len(path)) - (1)]]).StartAddress()
                    path = in49_
                    exits = in50_
                    c = in51_
                    xs = in52_
                    tgtPC = in53_
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
                    in54_ = xs
                    in55_ = pc
                    in56_ = (rank) + (1)
                    xs = in54_
                    pc = in55_
                    rank = in56_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def EquivSeg(s1, s2):
        source44_ = s1
        if source44_.is_JUMPSeg:
            d_655___mcc_h0_ = source44_.ins
            d_656___mcc_h1_ = source44_.lastIns
            d_657___mcc_h2_ = source44_.netOpEffect
            def lambda33_(forall_var_4_):
                d_658_i_: int = forall_var_4_
                return not (((0) <= (d_658_i_)) and ((d_658_i_) < ((len((s1).ins)) - (1)))) or ((((s1).ins)[d_658_i_]).Equiv(((s2).ins)[d_658_i_]))

            return ((((s2).is_JUMPSeg) and (((len((s1).Ins())) == (len((s2).Ins()))) and ((len((s2).Ins())) >= (2)))) and ((((EVMConstants.default__.PUSH1) <= (((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode)) and ((((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode) == (((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode))) and ((((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode) <= (EVMConstants.default__.PUSH32)))) and (_dafny.quantifier(_dafny.IntegerRange(0, (len((s1).ins)) - (1)), True, lambda33_))
        elif source44_.is_JUMPISeg:
            d_659___mcc_h3_ = source44_.ins
            d_660___mcc_h4_ = source44_.lastIns
            d_661___mcc_h5_ = source44_.netOpEffect
            def lambda34_(forall_var_5_):
                d_662_i_: int = forall_var_5_
                return not (((0) <= (d_662_i_)) and ((d_662_i_) < ((len((s1).ins)) - (1)))) or ((((s1).ins)[d_662_i_]).Equiv(((s2).ins)[d_662_i_]))

            return ((((s2).is_JUMPISeg) and (((len((s1).Ins())) == (len((s2).Ins()))) and ((len((s2).Ins())) >= (2)))) and ((((EVMConstants.default__.PUSH1) <= (((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode)) and ((((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode) == (((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode))) and ((((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode) <= (EVMConstants.default__.PUSH32)))) and (_dafny.quantifier(_dafny.IntegerRange(0, (len((s1).ins)) - (1)), True, lambda34_))
        elif source44_.is_RETURNSeg:
            d_663___mcc_h6_ = source44_.ins
            d_664___mcc_h7_ = source44_.lastIns
            d_665___mcc_h8_ = source44_.netOpEffect
            def lambda35_(forall_var_6_):
                d_666_i_: int = forall_var_6_
                return not (((0) <= (d_666_i_)) and ((d_666_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_666_i_]).Equiv(((s2).Ins())[d_666_i_]))

            return (((s2).is_RETURNSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda35_))
        elif source44_.is_STOPSeg:
            d_667___mcc_h9_ = source44_.ins
            d_668___mcc_h10_ = source44_.lastIns
            d_669___mcc_h11_ = source44_.netOpEffect
            def lambda36_(forall_var_7_):
                d_670_i_: int = forall_var_7_
                return not (((0) <= (d_670_i_)) and ((d_670_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_670_i_]).Equiv(((s2).Ins())[d_670_i_]))

            return (((s2).is_STOPSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda36_))
        elif source44_.is_CONTSeg:
            d_671___mcc_h12_ = source44_.ins
            d_672___mcc_h13_ = source44_.lastIns
            d_673___mcc_h14_ = source44_.netOpEffect
            def lambda37_(forall_var_8_):
                d_674_i_: int = forall_var_8_
                return not (((0) <= (d_674_i_)) and ((d_674_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_674_i_]).Equiv(((s2).Ins())[d_674_i_]))

            return (((s2).is_CONTSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda37_))
        elif True:
            d_675___mcc_h15_ = source44_.ins
            d_676___mcc_h16_ = source44_.lastIns
            d_677___mcc_h17_ = source44_.netOpEffect
            def lambda38_(forall_var_9_):
                d_678_i_: int = forall_var_9_
                return not (((0) <= (d_678_i_)) and ((d_678_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_678_i_]).Equiv(((s2).Ins())[d_678_i_]))

            return (((s2).is_INVALIDSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda38_))


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
            d_679___mcc_h0_ = source45_.ins
            d_680___mcc_h1_ = source45_.lastIns
            d_681___mcc_h2_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMP)
        elif source45_.is_JUMPISeg:
            d_682___mcc_h3_ = source45_.ins
            d_683___mcc_h4_ = source45_.lastIns
            d_684___mcc_h5_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.JUMPI)
        elif source45_.is_RETURNSeg:
            d_685___mcc_h6_ = source45_.ins
            d_686___mcc_h7_ = source45_.lastIns
            d_687___mcc_h8_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.RETURN)
        elif source45_.is_STOPSeg:
            d_688___mcc_h9_ = source45_.ins
            d_689___mcc_h10_ = source45_.lastIns
            d_690___mcc_h11_ = source45_.netOpEffect
            return (((((self).lastIns).op).opcode) == (EVMConstants.default__.STOP)) or (((((self).lastIns).op).opcode) == (EVMConstants.default__.REVERT))
        elif source45_.is_CONTSeg:
            d_691___mcc_h12_ = source45_.ins
            d_692___mcc_h13_ = source45_.lastIns
            d_693___mcc_h14_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) != (EVMConstants.default__.INVALID)
        elif True:
            d_694___mcc_h15_ = source45_.ins
            d_695___mcc_h16_ = source45_.lastIns
            d_696___mcc_h17_ = source45_.netOpEffect
            return ((((self).lastIns).op).opcode) == (EVMConstants.default__.INVALID)

    def Ins(self):
        return ((self).ins) + (_dafny.SeqWithoutIsStrInference([(self).lastIns]))

    def Size(self, xi):
        d_697___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (0) + (d_697___accumulator_)
                elif True:
                    d_697___accumulator_ = (d_697___accumulator_) + (((xi)[0]).Size())
                    in57_ = _this
                    in58_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    _this = in57_
                    
                    xi = in58_
                    raise _dafny.TailCall()
                break

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
        d_698___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(rest)) == (0):
                    return (d_698___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif ((((rest)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    d_698___accumulator_ = (d_698___accumulator_) + (_dafny.SeqWithoutIsStrInference([((rest)[0]).address]))
                    in59_ = _this
                    in60_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in59_
                    
                    rest = in60_
                    raise _dafny.TailCall()
                elif True:
                    in61_ = _this
                    in62_ = _dafny.SeqWithoutIsStrInference((rest)[1::])
                    _this = in61_
                    
                    rest = in62_
                    raise _dafny.TailCall()
                break

    def WeakestPreOperands(self, n):
        return default__.WeakestPreOperandsHelper((self).Ins(), n)

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), n)

    def Run(self, s, exit, jumpDests):
        d_699_s_k_ = default__.RunIns((self).ins, s, jumpDests)
        if (d_699_s_k_).is_Error:
            return d_699_s_k_
        elif True:
            return ((self).lastIns).NextState(d_699_s_k_, jumpDests, exit)

    def WPre(self, c):
        return default__.WPreIns((self).Ins(), c)

    def HasExit(self, b):
        source46_ = self
        if source46_.is_JUMPSeg:
            d_700___mcc_h0_ = source46_.ins
            d_701___mcc_h1_ = source46_.lastIns
            d_702___mcc_h2_ = source46_.netOpEffect
            return b
        elif source46_.is_JUMPISeg:
            d_703___mcc_h6_ = source46_.ins
            d_704___mcc_h7_ = source46_.lastIns
            d_705___mcc_h8_ = source46_.netOpEffect
            return True
        elif source46_.is_RETURNSeg:
            d_706___mcc_h12_ = source46_.ins
            d_707___mcc_h13_ = source46_.lastIns
            d_708___mcc_h14_ = source46_.netOpEffect
            return False
        elif source46_.is_STOPSeg:
            d_709___mcc_h18_ = source46_.ins
            d_710___mcc_h19_ = source46_.lastIns
            d_711___mcc_h20_ = source46_.netOpEffect
            return False
        elif source46_.is_CONTSeg:
            d_712___mcc_h24_ = source46_.ins
            d_713___mcc_h25_ = source46_.lastIns
            d_714___mcc_h26_ = source46_.netOpEffect
            return not(b)
        elif True:
            d_715___mcc_h30_ = source46_.ins
            d_716___mcc_h31_ = source46_.lastIns
            d_717___mcc_h32_ = source46_.netOpEffect
            return False

    def LeadsTo(self, k, exit):
        if (k) >= (Int.default__.TWO__256):
            return WeakPre.Cond_StFalse()
        elif True:
            source47_ = self
            if source47_.is_JUMPSeg:
                d_718___mcc_h0_ = source47_.ins
                d_719___mcc_h1_ = source47_.lastIns
                d_720___mcc_h2_ = source47_.netOpEffect
                if exit:
                    d_721_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                    return default__.WPreIns((self).ins, d_721_c_)
                elif True:
                    return WeakPre.Cond_StFalse()
            elif source47_.is_JUMPISeg:
                d_722___mcc_h3_ = source47_.ins
                d_723___mcc_h4_ = source47_.lastIns
                d_724___mcc_h5_ = source47_.netOpEffect
                if exit:
                    d_725_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                    return default__.WPreIns((self).ins, d_725_c_)
                elif (k) == ((self).StartAddressNextSeg()):
                    return WeakPre.Cond_StTrue()
                elif True:
                    return WeakPre.Cond_StFalse()
            elif source47_.is_RETURNSeg:
                d_726___mcc_h6_ = source47_.ins
                d_727___mcc_h7_ = source47_.lastIns
                d_728___mcc_h8_ = source47_.netOpEffect
                return WeakPre.Cond_StTrue()
            elif source47_.is_STOPSeg:
                d_729___mcc_h9_ = source47_.ins
                d_730___mcc_h10_ = source47_.lastIns
                d_731___mcc_h11_ = source47_.netOpEffect
                return WeakPre.Cond_StTrue()
            elif source47_.is_CONTSeg:
                d_732___mcc_h12_ = source47_.ins
                d_733___mcc_h13_ = source47_.lastIns
                d_734___mcc_h14_ = source47_.netOpEffect
                if (not(exit)) and ((k) == ((self).StartAddressNextSeg())):
                    return WeakPre.Cond_StTrue()
                elif True:
                    return WeakPre.Cond_StFalse()
            elif True:
                d_735___mcc_h15_ = source47_.ins
                d_736___mcc_h16_ = source47_.lastIns
                d_737___mcc_h17_ = source47_.netOpEffect
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

