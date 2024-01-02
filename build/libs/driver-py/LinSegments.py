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
        d_650___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_650___accumulator_)
                elif True:
                    d_650___accumulator_ = (d_650___accumulator_) + (((xs)[0]).StackEffect())
                    in41_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in41_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreOperandsHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_651_lastI_ = (xs)[(len(xs)) - (1)]
                    d_652_e_ = (d_651_lastI_).WeakestPreOperands(postCond)
                    in42_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in43_ = d_652_e_
                    xs = in42_
                    postCond = in43_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreCapacityHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_653_lastI_ = (xs)[(len(xs)) - (1)]
                    d_654_e_ = (d_653_lastI_).WeakestPreCapacity(postCond)
                    in44_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in45_ = d_654_e_
                    xs = in44_
                    postCond = in45_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def RunIns(xs, s, jumpDests):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return s
                elif True:
                    d_655_next_ = ((xs)[0]).NextState(s, jumpDests, 0)
                    source43_ = d_655_next_
                    if source43_.is_EState:
                        d_656___mcc_h0_ = source43_.pc
                        d_657___mcc_h1_ = source43_.stack
                        in46_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in47_ = d_655_next_
                        in48_ = jumpDests
                        xs = in46_
                        s = in47_
                        jumpDests = in48_
                        raise _dafny.TailCall()
                    elif True:
                        d_658___mcc_h2_ = source43_.msg
                        return d_655_next_
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
                    d_659_c1_ = ((xs)[(len(xs)) - (1)]).WPre(c)
                    in49_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in50_ = d_659_c1_
                    xs = in49_
                    c = in50_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WPreSeqSegs(path, exits, c, xs, tgtPC):
        while True:
            with _dafny.label():
                if (len(path)) == (0):
                    return c
                elif True:
                    d_660_w1_ = ((xs)[(path)[(len(path)) - (1)]]).WPre(c)
                    d_661_wp2_ = ((xs)[(path)[(len(path)) - (1)]]).LeadsTo(tgtPC, (exits)[(len(exits)) - (1)])
                    in51_ = _dafny.SeqWithoutIsStrInference((path)[:(len(path)) - (1):])
                    in52_ = _dafny.SeqWithoutIsStrInference((exits)[:(len(exits)) - (1):])
                    in53_ = (d_660_w1_).And(d_661_wp2_)
                    in54_ = xs
                    in55_ = ((xs)[(path)[(len(path)) - (1)]]).StartAddress()
                    path = in51_
                    exits = in52_
                    c = in53_
                    xs = in54_
                    tgtPC = in55_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def EquivSeg(s1, s2):
        source44_ = s1
        if source44_.is_JUMPSeg:
            d_662___mcc_h0_ = source44_.ins
            d_663___mcc_h1_ = source44_.lastIns
            d_664___mcc_h2_ = source44_.netOpEffect
            def lambda35_(forall_var_3_):
                d_665_i_: int = forall_var_3_
                return not (((0) <= (d_665_i_)) and ((d_665_i_) < ((len((s1).ins)) - (1)))) or ((((s1).ins)[d_665_i_]).Equiv(((s2).ins)[d_665_i_]))

            return ((((s2).is_JUMPSeg) and (((len((s1).Ins())) == (len((s2).Ins()))) and ((len((s2).Ins())) >= (2)))) and ((((EVMConstants.default__.PUSH1) <= (((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode)) and ((((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode) == (((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode))) and ((((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode) <= (EVMConstants.default__.PUSH32)))) and (_dafny.quantifier(_dafny.IntegerRange(0, (len((s1).ins)) - (1)), True, lambda35_))
        elif source44_.is_JUMPISeg:
            d_666___mcc_h3_ = source44_.ins
            d_667___mcc_h4_ = source44_.lastIns
            d_668___mcc_h5_ = source44_.netOpEffect
            def lambda36_(forall_var_4_):
                d_669_i_: int = forall_var_4_
                return not (((0) <= (d_669_i_)) and ((d_669_i_) < ((len((s1).ins)) - (1)))) or ((((s1).ins)[d_669_i_]).Equiv(((s2).ins)[d_669_i_]))

            return ((((s2).is_JUMPISeg) and (((len((s1).Ins())) == (len((s2).Ins()))) and ((len((s2).Ins())) >= (2)))) and ((((EVMConstants.default__.PUSH1) <= (((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode)) and ((((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode) == (((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode))) and ((((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode) <= (EVMConstants.default__.PUSH32)))) and (_dafny.quantifier(_dafny.IntegerRange(0, (len((s1).ins)) - (1)), True, lambda36_))
        elif source44_.is_RETURNSeg:
            d_670___mcc_h6_ = source44_.ins
            d_671___mcc_h7_ = source44_.lastIns
            d_672___mcc_h8_ = source44_.netOpEffect
            def lambda37_(forall_var_5_):
                d_673_i_: int = forall_var_5_
                return not (((0) <= (d_673_i_)) and ((d_673_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_673_i_]).Equiv(((s2).Ins())[d_673_i_]))

            return (((s2).is_RETURNSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda37_))
        elif source44_.is_STOPSeg:
            d_674___mcc_h9_ = source44_.ins
            d_675___mcc_h10_ = source44_.lastIns
            d_676___mcc_h11_ = source44_.netOpEffect
            def lambda38_(forall_var_6_):
                d_677_i_: int = forall_var_6_
                return not (((0) <= (d_677_i_)) and ((d_677_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_677_i_]).Equiv(((s2).Ins())[d_677_i_]))

            return (((s2).is_STOPSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda38_))
        elif source44_.is_CONTSeg:
            d_678___mcc_h12_ = source44_.ins
            d_679___mcc_h13_ = source44_.lastIns
            d_680___mcc_h14_ = source44_.netOpEffect
            def lambda39_(forall_var_7_):
                d_681_i_: int = forall_var_7_
                return not (((0) <= (d_681_i_)) and ((d_681_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_681_i_]).Equiv(((s2).Ins())[d_681_i_]))

            return (((s2).is_CONTSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda39_))
        elif True:
            d_682___mcc_h15_ = source44_.ins
            d_683___mcc_h16_ = source44_.lastIns
            d_684___mcc_h17_ = source44_.netOpEffect
            def lambda40_(forall_var_8_):
                d_685_i_: int = forall_var_8_
                return not (((0) <= (d_685_i_)) and ((d_685_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_685_i_]).Equiv(((s2).Ins())[d_685_i_]))

            return (((s2).is_INVALIDSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda40_))


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
    def Ins(self):
        return ((self).ins) + (_dafny.SeqWithoutIsStrInference([(self).lastIns]))

    def Size(self, xi):
        d_686___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (0) + (d_686___accumulator_)
                elif True:
                    d_686___accumulator_ = (d_686___accumulator_) + (((xi)[0]).Size())
                    in56_ = _this
                    in57_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    _this = in56_
                    
                    xi = in57_
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

    def CollectJumpDest(self):
        if (((((self).Ins())[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
            return _dafny.SeqWithoutIsStrInference([(((self).Ins())[0]).address])
        elif True:
            return _dafny.SeqWithoutIsStrInference([])

    def WeakestPreOperands(self, n):
        return default__.WeakestPreOperandsHelper((self).Ins(), n)

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), n)

    def Run(self, s, exit, jumpDests):
        d_687_s_k_ = default__.RunIns((self).ins, s, jumpDests)
        if (d_687_s_k_).is_Error:
            return d_687_s_k_
        elif True:
            return ((self).lastIns).NextState(d_687_s_k_, jumpDests, exit)

    def WPre(self, c):
        return default__.WPreIns((self).Ins(), c)

    def NumberOfExits(self):
        source45_ = self
        if source45_.is_JUMPSeg:
            d_688___mcc_h0_ = source45_.ins
            d_689___mcc_h1_ = source45_.lastIns
            d_690___mcc_h2_ = source45_.netOpEffect
            return 1
        elif source45_.is_JUMPISeg:
            d_691___mcc_h6_ = source45_.ins
            d_692___mcc_h7_ = source45_.lastIns
            d_693___mcc_h8_ = source45_.netOpEffect
            return 2
        elif source45_.is_RETURNSeg:
            d_694___mcc_h12_ = source45_.ins
            d_695___mcc_h13_ = source45_.lastIns
            d_696___mcc_h14_ = source45_.netOpEffect
            return 0
        elif source45_.is_STOPSeg:
            d_697___mcc_h18_ = source45_.ins
            d_698___mcc_h19_ = source45_.lastIns
            d_699___mcc_h20_ = source45_.netOpEffect
            return 0
        elif source45_.is_CONTSeg:
            d_700___mcc_h24_ = source45_.ins
            d_701___mcc_h25_ = source45_.lastIns
            d_702___mcc_h26_ = source45_.netOpEffect
            return 1
        elif True:
            d_703___mcc_h30_ = source45_.ins
            d_704___mcc_h31_ = source45_.lastIns
            d_705___mcc_h32_ = source45_.netOpEffect
            return 0

    def IsJump(self):
        return ((self).is_JUMPSeg) or ((self).is_JUMPISeg)

    def LeadsTo(self, k, exit):
        if (k) >= (Int.default__.TWO__256):
            return WeakPre.Cond_StFalse()
        elif True:
            source46_ = self
            if source46_.is_JUMPSeg:
                d_706___mcc_h0_ = source46_.ins
                d_707___mcc_h1_ = source46_.lastIns
                d_708___mcc_h2_ = source46_.netOpEffect
                if (exit) == (0):
                    d_709_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                    return default__.WPreIns((self).ins, d_709_c_)
                elif True:
                    return WeakPre.Cond_StFalse()
            elif source46_.is_JUMPISeg:
                d_710___mcc_h3_ = source46_.ins
                d_711___mcc_h4_ = source46_.lastIns
                d_712___mcc_h5_ = source46_.netOpEffect
                if (exit) == (1):
                    d_713_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                    return default__.WPreIns((self).ins, d_713_c_)
                elif (k) == ((self).StartAddressNextSeg()):
                    return WeakPre.Cond_StTrue()
                elif True:
                    return WeakPre.Cond_StFalse()
            elif source46_.is_RETURNSeg:
                d_714___mcc_h6_ = source46_.ins
                d_715___mcc_h7_ = source46_.lastIns
                d_716___mcc_h8_ = source46_.netOpEffect
                return WeakPre.Cond_StTrue()
            elif source46_.is_STOPSeg:
                d_717___mcc_h9_ = source46_.ins
                d_718___mcc_h10_ = source46_.lastIns
                d_719___mcc_h11_ = source46_.netOpEffect
                return WeakPre.Cond_StTrue()
            elif source46_.is_CONTSeg:
                d_720___mcc_h12_ = source46_.ins
                d_721___mcc_h13_ = source46_.lastIns
                d_722___mcc_h14_ = source46_.netOpEffect
                if ((exit) == (0)) and ((k) == ((self).StartAddressNextSeg())):
                    return WeakPre.Cond_StTrue()
                elif True:
                    return WeakPre.Cond_StFalse()
            elif True:
                d_723___mcc_h15_ = source46_.ins
                d_724___mcc_h16_ = source46_.lastIns
                d_725___mcc_h17_ = source46_.netOpEffect
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

