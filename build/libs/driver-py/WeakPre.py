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

# Module: WeakPre

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Merge(c1, c2):
        while True:
            with _dafny.label():
                if ((c2).Size()) == (0):
                    return c1
                elif ((c2).Size()) == (1):
                    if (((c2).trackedPos)[0]) in ((c1).trackedPos):
                        d_131_i_ = default__.FindVal(((c2).trackedPos)[0], (c1).trackedPos, 0)
                        if (((c1).trackedVals)[d_131_i_]) == (((c2).trackedVals)[0]):
                            return c1
                        elif True:
                            return Cond_StFalse()
                    elif True:
                        return Cond_StCond(((c1).trackedPos) + (_dafny.SeqWithoutIsStrInference([((c2).trackedPos)[0]])), ((c1).trackedVals) + (_dafny.SeqWithoutIsStrInference([((c2).trackedVals)[0]])))
                elif True:
                    if (((c2).trackedPos)[0]) in ((c1).trackedPos):
                        in13_ = c1
                        in14_ = Cond_StCond(_dafny.SeqWithoutIsStrInference(((c2).trackedPos)[1::]), _dafny.SeqWithoutIsStrInference(((c2).trackedVals)[1::]))
                        c1 = in13_
                        c2 = in14_
                        raise _dafny.TailCall()
                    elif True:
                        d_132_p_ = ((c1).trackedPos) + (_dafny.SeqWithoutIsStrInference([((c2).trackedPos)[0]]))
                        d_133_v_ = ((c1).trackedVals) + (_dafny.SeqWithoutIsStrInference([((c2).trackedVals)[0]]))
                        in15_ = Cond_StCond(d_132_p_, d_133_v_)
                        in16_ = Cond_StCond(_dafny.SeqWithoutIsStrInference(((c2).trackedPos)[1::]), _dafny.SeqWithoutIsStrInference(((c2).trackedVals)[1::]))
                        c1 = in15_
                        c2 = in16_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def FindVal(x, xs, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (1):
                    return index
                elif ((xs)[index]) == (x):
                    return index
                elif True:
                    in17_ = x
                    in18_ = xs
                    in19_ = (index) + (1)
                    x = in17_
                    xs = in18_
                    index = in19_
                    raise _dafny.TailCall()
                break


class ValidCond:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Cond_StCond(_dafny.SeqWithoutIsStrInference([1]), _dafny.SeqWithoutIsStrInference([0]))

class Cond:
    @classmethod
    def default(cls, ):
        return lambda: Cond_StTrue()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_StTrue(self) -> bool:
        return isinstance(self, Cond_StTrue)
    @property
    def is_StFalse(self) -> bool:
        return isinstance(self, Cond_StFalse)
    @property
    def is_StCond(self) -> bool:
        return isinstance(self, Cond_StCond)
    def IsValid(self):
        def lambda1_(forall_var_1_):
            def lambda2_(forall_var_2_):
                d_135_k_k_: int = forall_var_2_
                return not ((((0) <= (d_134_k_)) and ((d_134_k_) < (d_135_k_k_))) and ((d_135_k_k_) < (len((self).trackedPos)))) or ((((self).trackedPos)[d_134_k_]) != (((self).trackedPos)[d_135_k_k_]))

            d_134_k_: int = forall_var_1_
            return _dafny.quantifier(_dafny.IntegerRange((d_134_k_) + (1), len((self).trackedPos)), True, lambda2_)

        return not ((self).is_StCond) or ((((len((self).trackedPos)) == (len((self).trackedVals))) and ((len((self).trackedVals)) > (0))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).trackedPos)), True, lambda1_)))

    def Size(self):
        if (self).is_StCond:
            return len((self).trackedPos)
        elif True:
            return 0

    def And(self, c):
        source27_ = (self, c)
        d_136___mcc_h0_ = source27_[0]
        d_137___mcc_h1_ = source27_[1]
        source28_ = d_136___mcc_h0_
        if source28_.is_StTrue:
            source29_ = d_137___mcc_h1_
            if source29_.is_StTrue:
                d_138_cond_ = d_137___mcc_h1_
                return d_138_cond_
            elif source29_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_139___mcc_h2_ = source29_.trackedPos
                d_140___mcc_h3_ = source29_.trackedVals
                d_141_cond_ = d_137___mcc_h1_
                return d_141_cond_
        elif source28_.is_StFalse:
            source30_ = d_137___mcc_h1_
            if source30_.is_StTrue:
                return Cond_StFalse()
            elif source30_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_142___mcc_h8_ = source30_.trackedPos
                d_143___mcc_h9_ = source30_.trackedVals
                return Cond_StFalse()
        elif True:
            d_144___mcc_h14_ = source28_.trackedPos
            d_145___mcc_h15_ = source28_.trackedVals
            source31_ = d_137___mcc_h1_
            if source31_.is_StTrue:
                d_146_c1_ = d_136___mcc_h0_
                return d_146_c1_
            elif source31_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_147___mcc_h22_ = source31_.trackedPos
                d_148___mcc_h23_ = source31_.trackedVals
                d_149_c2_ = d_137___mcc_h1_
                d_150_c1_ = d_136___mcc_h0_
                return default__.Merge(d_150_c1_, d_149_c2_)

    def TrackedPos(self):
        return (self).trackedPos

    def TrackedVals(self):
        return (self).trackedVals

    def TrackedPosAt(self, i):
        return ((self).trackedPos)[i]

    def TrackedValAt(self, i):
        return ((self).trackedVals)[i]

    def Tail(self):
        d_151_dt__update__tmp_h0_ = self
        d_152_dt__update_htrackedVals_h0_ = _dafny.SeqWithoutIsStrInference(((self).trackedVals)[1::])
        d_153_dt__update_htrackedPos_h0_ = _dafny.SeqWithoutIsStrInference(((self).trackedPos)[1::])
        return Cond_StCond(d_153_dt__update_htrackedPos_h0_, d_152_dt__update_htrackedVals_h0_)

    def Add(self, pos, val):
        return self

    def BuildStack(self, r, index):
        _this = self
        while True:
            with _dafny.label():
                if (index) == (len((_this).trackedPos)):
                    return r
                elif (((_this).trackedPos)[index]) < (len(r)):
                    in20_ = _this
                    in21_ = (r).set(((_this).trackedPos)[index], StackElement.StackElem_Value(((_this).trackedVals)[index]))
                    in22_ = (index) + (1)
                    _this = in20_
                    
                    r = in21_
                    index = in22_
                    raise _dafny.TailCall()
                elif True:
                    d_154_suf_ = _dafny.SeqWithoutIsStrInference([StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) for d_155___v2_ in range((((_this).trackedPos)[index]) - (len(r)))])
                    in23_ = _this
                    in24_ = ((r) + (d_154_suf_)) + (_dafny.SeqWithoutIsStrInference([StackElement.StackElem_Value(((_this).trackedVals)[index])]))
                    in25_ = (index) + (1)
                    _this = in23_
                    
                    r = in24_
                    index = in25_
                    raise _dafny.TailCall()
                break


class Cond_StTrue(Cond, NamedTuple('StTrue', [])):
    def __dafnystr__(self) -> str:
        return f'WeakPre.Cond.StTrue'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Cond_StTrue)
    def __hash__(self) -> int:
        return super().__hash__()

class Cond_StFalse(Cond, NamedTuple('StFalse', [])):
    def __dafnystr__(self) -> str:
        return f'WeakPre.Cond.StFalse'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Cond_StFalse)
    def __hash__(self) -> int:
        return super().__hash__()

class Cond_StCond(Cond, NamedTuple('StCond', [('trackedPos', Any), ('trackedVals', Any)])):
    def __dafnystr__(self) -> str:
        return f'WeakPre.Cond.StCond({_dafny.string_of(self.trackedPos)}, {_dafny.string_of(self.trackedVals)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Cond_StCond) and self.trackedPos == __o.trackedPos and self.trackedVals == __o.trackedVals
    def __hash__(self) -> int:
        return super().__hash__()

