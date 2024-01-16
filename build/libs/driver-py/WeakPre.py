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
    def StackToCond(xs):
        d_143_r_ = default__.StackToCondHelper(xs, (_dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([])), 0)
        if (len((d_143_r_)[0])) == (0):
            return Cond_StTrue()
        elif True:
            return Cond_StCond((d_143_r_)[0], (d_143_r_)[1])

    @staticmethod
    def StackToCondHelper(xs, c, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return c
                elif ((xs)[index]).is_Value:
                    d_144_c_k_ = (((c)[0]) + (_dafny.SeqWithoutIsStrInference([index])), ((c)[1]) + (_dafny.SeqWithoutIsStrInference([((xs)[index]).v])))
                    in19_ = xs
                    in20_ = d_144_c_k_
                    in21_ = (index) + (1)
                    xs = in19_
                    c = in20_
                    index = in21_
                    raise _dafny.TailCall()
                elif True:
                    in22_ = xs
                    in23_ = c
                    in24_ = (index) + (1)
                    xs = in22_
                    c = in23_
                    index = in24_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Merge(c1, c2):
        while True:
            with _dafny.label():
                if ((c2).Size()) == (0):
                    return c1
                elif ((c2).Size()) == (1):
                    if (((c2).trackedPos)[0]) in ((c1).trackedPos):
                        d_145_i_ = default__.FindVal(((c2).trackedPos)[0], (c1).trackedPos, 0)
                        if (((c1).trackedVals)[d_145_i_]) == (((c2).trackedVals)[0]):
                            return c1
                        elif True:
                            return Cond_StFalse()
                    elif True:
                        return Cond_StCond(((c1).trackedPos) + (_dafny.SeqWithoutIsStrInference([((c2).trackedPos)[0]])), ((c1).trackedVals) + (_dafny.SeqWithoutIsStrInference([((c2).trackedVals)[0]])))
                elif True:
                    if (((c2).trackedPos)[0]) in ((c1).trackedPos):
                        in25_ = c1
                        in26_ = Cond_StCond(_dafny.SeqWithoutIsStrInference(((c2).trackedPos)[1::]), _dafny.SeqWithoutIsStrInference(((c2).trackedVals)[1::]))
                        c1 = in25_
                        c2 = in26_
                        raise _dafny.TailCall()
                    elif True:
                        d_146_p_ = ((c1).trackedPos) + (_dafny.SeqWithoutIsStrInference([((c2).trackedPos)[0]]))
                        d_147_v_ = ((c1).trackedVals) + (_dafny.SeqWithoutIsStrInference([((c2).trackedVals)[0]]))
                        in27_ = Cond_StCond(d_146_p_, d_147_v_)
                        in28_ = Cond_StCond(_dafny.SeqWithoutIsStrInference(((c2).trackedPos)[1::]), _dafny.SeqWithoutIsStrInference(((c2).trackedVals)[1::]))
                        c1 = in27_
                        c2 = in28_
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
                    in29_ = x
                    in30_ = xs
                    in31_ = (index) + (1)
                    x = in29_
                    xs = in30_
                    index = in31_
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
        def lambda4_(forall_var_1_):
            def lambda5_(forall_var_2_):
                d_149_k_k_: int = forall_var_2_
                return not ((((0) <= (d_148_k_)) and ((d_148_k_) < (d_149_k_k_))) and ((d_149_k_k_) < (len((self).trackedPos)))) or ((((self).trackedPos)[d_148_k_]) != (((self).trackedPos)[d_149_k_k_]))

            d_148_k_: int = forall_var_1_
            return _dafny.quantifier(_dafny.IntegerRange((d_148_k_) + (1), len((self).trackedPos)), True, lambda5_)

        return not ((self).is_StCond) or ((((len((self).trackedPos)) == (len((self).trackedVals))) and ((len((self).trackedVals)) > (0))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).trackedPos)), True, lambda4_)))

    def Size(self):
        if (self).is_StCond:
            return len((self).trackedPos)
        elif True:
            return 0

    def And(self, c):
        source28_ = (self, c)
        d_150___mcc_h0_ = source28_[0]
        d_151___mcc_h1_ = source28_[1]
        source29_ = d_150___mcc_h0_
        if source29_.is_StTrue:
            source30_ = d_151___mcc_h1_
            if source30_.is_StTrue:
                d_152_cond_ = d_151___mcc_h1_
                return d_152_cond_
            elif source30_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_153___mcc_h2_ = source30_.trackedPos
                d_154___mcc_h3_ = source30_.trackedVals
                d_155_cond_ = d_151___mcc_h1_
                return d_155_cond_
        elif source29_.is_StFalse:
            source31_ = d_151___mcc_h1_
            if source31_.is_StTrue:
                return Cond_StFalse()
            elif source31_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_156___mcc_h8_ = source31_.trackedPos
                d_157___mcc_h9_ = source31_.trackedVals
                return Cond_StFalse()
        elif True:
            d_158___mcc_h14_ = source29_.trackedPos
            d_159___mcc_h15_ = source29_.trackedVals
            source32_ = d_151___mcc_h1_
            if source32_.is_StTrue:
                d_160_c1_ = d_150___mcc_h0_
                return d_160_c1_
            elif source32_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_161___mcc_h22_ = source32_.trackedPos
                d_162___mcc_h23_ = source32_.trackedVals
                d_163_c2_ = d_151___mcc_h1_
                d_164_c1_ = d_150___mcc_h0_
                return default__.Merge(d_164_c1_, d_163_c2_)

    def TrackedPos(self):
        return (self).trackedPos

    def TrackedVals(self):
        return (self).trackedVals

    def TrackedPosAt(self, i):
        return ((self).trackedPos)[i]

    def TrackedValAt(self, i):
        return ((self).trackedVals)[i]

    def Tail(self):
        d_165_dt__update__tmp_h0_ = self
        d_166_dt__update_htrackedVals_h0_ = _dafny.SeqWithoutIsStrInference(((self).trackedVals)[1::])
        d_167_dt__update_htrackedPos_h0_ = _dafny.SeqWithoutIsStrInference(((self).trackedPos)[1::])
        return Cond_StCond(d_167_dt__update_htrackedPos_h0_, d_166_dt__update_htrackedVals_h0_)

    def Add(self, pos, val):
        return self

    def BuildStack(self, r, index):
        _this = self
        while True:
            with _dafny.label():
                if (index) == (len((_this).trackedPos)):
                    return r
                elif (((_this).trackedPos)[index]) < (len(r)):
                    in32_ = _this
                    in33_ = (r).set(((_this).trackedPos)[index], StackElement.StackElem_Value(((_this).trackedVals)[index]))
                    in34_ = (index) + (1)
                    _this = in32_
                    
                    r = in33_
                    index = in34_
                    raise _dafny.TailCall()
                elif True:
                    d_168_suf_ = _dafny.SeqWithoutIsStrInference([StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) for d_169___v2_ in range((((_this).trackedPos)[index]) - (len(r)))])
                    in35_ = _this
                    in36_ = ((r) + (d_168_suf_)) + (_dafny.SeqWithoutIsStrInference([StackElement.StackElem_Value(((_this).trackedVals)[index])]))
                    in37_ = (index) + (1)
                    _this = in35_
                    
                    r = in36_
                    index = in37_
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

