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
import BinaryDecoder as BinaryDecoder

# Module: LinSegments

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def StackEffectHelper(xs):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (((xs)[0]).StackEffect())
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WeakestPreCapacityHelper(xs, postCond):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_0_lastI_ = (xs)[(len(xs)) - (1)]
                    d_1_e_ = (d_0_lastI_).WeakestPreCapacity(postCond)
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in1_ = d_1_e_
                    xs = in0_
                    postCond = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def RunIns(xs, s, jumpDests):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return s
                elif True:
                    d_0_next_ = ((xs)[0]).NextState(s, jumpDests, 0)
                    source0_ = d_0_next_
                    if True:
                        if source0_.is_Error:
                            return d_0_next_
                    if True:
                        in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in1_ = d_0_next_
                        in2_ = jumpDests
                        xs = in0_
                        s = in1_
                        jumpDests = in2_
                        raise _dafny.TailCall()
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
                    d_0_c1_ = ((xs)[(len(xs)) - (1)]).WPre(c)
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in1_ = d_0_c1_
                    xs = in0_
                    c = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WPreSeqSegs(path, exits, c, xs, tgtPC):
        while True:
            with _dafny.label():
                if (len(path)) == (0):
                    return c
                elif True:
                    d_0_w1_ = ((xs)[(path)[(len(path)) - (1)]]).WPre(c)
                    d_1_wp2_ = ((xs)[(path)[(len(path)) - (1)]]).LeadsTo(tgtPC, (exits)[(len(exits)) - (1)])
                    in0_ = _dafny.SeqWithoutIsStrInference((path)[:(len(path)) - (1):])
                    in1_ = _dafny.SeqWithoutIsStrInference((exits)[:(len(exits)) - (1):])
                    in2_ = (d_0_w1_).And(d_1_wp2_)
                    in3_ = xs
                    in4_ = ((xs)[(path)[(len(path)) - (1)]]).StartAddress()
                    path = in0_
                    exits = in1_
                    c = in2_
                    xs = in3_
                    tgtPC = in4_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def EquivSeg(s1, s2):
        source0_ = s1
        if True:
            if source0_.is_JUMPSeg:
                def lambda0_(forall_var_0_):
                    d_0_i_: int = forall_var_0_
                    return not (((0) <= (d_0_i_)) and ((d_0_i_) < ((len((s1).ins)) - (1)))) or ((((s1).ins)[d_0_i_]).Equiv(((s2).ins)[d_0_i_]))

                return ((((s2).is_JUMPSeg) and (((len((s1).Ins())) == (len((s2).Ins()))) and ((len((s2).Ins())) >= (2)))) and ((((EVMConstants.default__.PUSH1) <= (((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode)) and ((((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode) == (((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode))) and ((((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode) <= (EVMConstants.default__.PUSH32)))) and (_dafny.quantifier(_dafny.IntegerRange(0, (len((s1).ins)) - (1)), True, lambda0_))
        if True:
            if source0_.is_JUMPISeg:
                def lambda1_(forall_var_1_):
                    d_1_i_: int = forall_var_1_
                    return not (((0) <= (d_1_i_)) and ((d_1_i_) < ((len((s1).ins)) - (1)))) or ((((s1).ins)[d_1_i_]).Equiv(((s2).ins)[d_1_i_]))

                return ((((s2).is_JUMPISeg) and (((len((s1).Ins())) == (len((s2).Ins()))) and ((len((s2).Ins())) >= (2)))) and ((((EVMConstants.default__.PUSH1) <= (((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode)) and ((((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode) == (((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode))) and ((((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode) <= (EVMConstants.default__.PUSH32)))) and (_dafny.quantifier(_dafny.IntegerRange(0, (len((s1).ins)) - (1)), True, lambda1_))
        if True:
            if source0_.is_RETURNSeg:
                def lambda2_(forall_var_2_):
                    d_2_i_: int = forall_var_2_
                    return not (((0) <= (d_2_i_)) and ((d_2_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_2_i_]).Equiv(((s2).Ins())[d_2_i_]))

                return (((s2).is_RETURNSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda2_))
        if True:
            if source0_.is_STOPSeg:
                def lambda3_(forall_var_3_):
                    d_3_i_: int = forall_var_3_
                    return not (((0) <= (d_3_i_)) and ((d_3_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_3_i_]).Equiv(((s2).Ins())[d_3_i_]))

                return (((s2).is_STOPSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda3_))
        if True:
            if source0_.is_CONTSeg:
                def lambda4_(forall_var_4_):
                    d_4_i_: int = forall_var_4_
                    return not (((0) <= (d_4_i_)) and ((d_4_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_4_i_]).Equiv(((s2).Ins())[d_4_i_]))

                return (((s2).is_CONTSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda4_))
        if True:
            def lambda5_(forall_var_5_):
                d_5_i_: int = forall_var_5_
                return not (((0) <= (d_5_i_)) and ((d_5_i_) < (len((s1).Ins())))) or ((((s1).Ins())[d_5_i_]).Equiv(((s2).Ins())[d_5_i_]))

            return (((s2).is_INVALIDSeg) and ((len((s1).Ins())) == (len((s2).Ins())))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((s1).Ins())), True, lambda5_))


class ValidLinSeg:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return LinSeg_CONTSeg(_dafny.SeqWithoutIsStrInference([]), Instructions.Instruction_Instruction(EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ADD")), EVMConstants.default__.ADD, 0, 2, 1, 2), _dafny.SeqWithoutIsStrInference([]), 0), default__.StackEffectHelper((_dafny.SeqWithoutIsStrInference([])) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(EVMOpcodes.Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ADD")), EVMConstants.default__.ADD, 0, 2, 1, 2), _dafny.SeqWithoutIsStrInference([]), 0)]))))

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
        d_0___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (((xi)[0]).Size())
                    in0_ = _this
                    in1_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    _this = in0_
                    
                    xi = in1_
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

    def WeakestPreOperands(self, xs, postCond):
        _this = self
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return postCond
                elif True:
                    d_0_lastI_ = (xs)[(len(xs)) - (1)]
                    d_1_e_ = (d_0_lastI_).WeakestPreOperands(postCond)
                    in0_ = _this
                    in1_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in2_ = d_1_e_
                    _this = in0_
                    
                    xs = in1_
                    postCond = in2_
                    raise _dafny.TailCall()
                break

    def FastWeakestPreOperands(self, k, wpre0):
        if (k) <= ((self).StackEffect()):
            return wpre0
        elif True:
            return Int.default__.Max(wpre0, (k) - ((self).StackEffect()))

    def WeakestPreCapacity(self, n):
        return default__.WeakestPreCapacityHelper((self).Ins(), n)

    def Run(self, s, exit, jumpDests):
        d_0_s_k_ = default__.RunIns((self).ins, s, jumpDests)
        if (d_0_s_k_).is_Error:
            return d_0_s_k_
        elif True:
            return ((self).lastIns).NextState(d_0_s_k_, jumpDests, exit)

    def WPre(self, c):
        return default__.WPreIns((self).Ins(), c)

    def NumberOfExits(self):
        source0_ = self
        if True:
            if source0_.is_JUMPISeg:
                return 2
        if True:
            if source0_.is_JUMPSeg:
                return 1
        if True:
            if source0_.is_CONTSeg:
                return 1
        if True:
            return 0

    def IsJump(self):
        return ((self).is_JUMPSeg) or ((self).is_JUMPISeg)

    def LeadsTo(self, k, exit):
        if (k) >= (Int.default__.TWO__256):
            return WeakPre.Cond_StFalse()
        elif True:
            source0_ = self
            if True:
                if source0_.is_JUMPSeg:
                    if (exit) == (0):
                        d_0_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                        return default__.WPreIns((self).ins, d_0_c_)
                    elif True:
                        return WeakPre.Cond_StFalse()
            if True:
                if source0_.is_JUMPISeg:
                    if (exit) == (1):
                        d_1_c_ = WeakPre.Cond_StCond(_dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([k]))
                        return default__.WPreIns((self).ins, d_1_c_)
                    elif (k) == ((self).StartAddressNextSeg()):
                        return WeakPre.Cond_StTrue()
                    elif True:
                        return WeakPre.Cond_StFalse()
            if True:
                if source0_.is_CONTSeg:
                    if ((exit) == (0)) and ((k) == ((self).StartAddressNextSeg())):
                        return WeakPre.Cond_StTrue()
                    elif True:
                        return WeakPre.Cond_StFalse()
            if True:
                if source0_.is_RETURNSeg:
                    return WeakPre.Cond_StTrue()
            if True:
                if source0_.is_STOPSeg:
                    return WeakPre.Cond_StTrue()
            if True:
                return WeakPre.Cond_StFalse()

    def SegTypeName(self):
        source0_ = self
        if True:
            if source0_.is_JUMPSeg:
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMP Segment"))
        if True:
            if source0_.is_JUMPISeg:
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMPI Segment"))
        if True:
            if source0_.is_RETURNSeg:
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RETURN Segment"))
        if True:
            if source0_.is_STOPSeg:
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "STOP Segment"))
        if True:
            if source0_.is_CONTSeg:
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT Segment"))
        if True:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "INVALID Segment"))


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

