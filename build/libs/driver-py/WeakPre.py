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
                        d_126_i_ = default__.FindVal(((c2).trackedPos)[0], (c1).trackedPos, 0)
                        if (((c1).trackedVals)[d_126_i_]) == (((c2).trackedVals)[0]):
                            return c1
                        elif True:
                            return Cond_StFalse()
                    elif True:
                        return Cond_StCond(((c1).trackedPos) + (_dafny.SeqWithoutIsStrInference([((c2).trackedPos)[0]])), ((c1).trackedVals) + (_dafny.SeqWithoutIsStrInference([((c2).trackedVals)[0]])))
                elif True:
                    if (((c2).trackedPos)[0]) in ((c1).trackedPos):
                        in11_ = c1
                        in12_ = Cond_StCond(_dafny.SeqWithoutIsStrInference(((c2).trackedPos)[1::]), _dafny.SeqWithoutIsStrInference(((c2).trackedVals)[1::]))
                        c1 = in11_
                        c2 = in12_
                        raise _dafny.TailCall()
                    elif True:
                        d_127_p_ = ((c1).trackedPos) + (_dafny.SeqWithoutIsStrInference([((c2).trackedPos)[0]]))
                        d_128_v_ = ((c1).trackedVals) + (_dafny.SeqWithoutIsStrInference([((c2).trackedVals)[0]]))
                        in13_ = Cond_StCond(d_127_p_, d_128_v_)
                        in14_ = Cond_StCond(_dafny.SeqWithoutIsStrInference(((c2).trackedPos)[1::]), _dafny.SeqWithoutIsStrInference(((c2).trackedVals)[1::]))
                        c1 = in13_
                        c2 = in14_
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
                    in15_ = x
                    in16_ = xs
                    in17_ = (index) + (1)
                    x = in15_
                    xs = in16_
                    index = in17_
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
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                d_130_k_k_: int = forall_var_1_
                return not ((((0) <= (d_129_k_)) and ((d_129_k_) < (d_130_k_k_))) and ((d_130_k_k_) < (len((self).trackedPos)))) or ((((self).trackedPos)[d_129_k_]) != (((self).trackedPos)[d_130_k_k_]))

            d_129_k_: int = forall_var_0_
            return _dafny.quantifier(_dafny.IntegerRange((d_129_k_) + (1), len((self).trackedPos)), True, lambda1_)

        return not ((self).is_StCond) or ((((len((self).trackedPos)) == (len((self).trackedVals))) and ((len((self).trackedVals)) > (0))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).trackedPos)), True, lambda0_)))

    def Size(self):
        if (self).is_StCond:
            return len((self).trackedPos)
        elif True:
            return 0

    def And(self, c):
        source26_ = (self, c)
        d_131___mcc_h0_ = source26_[0]
        d_132___mcc_h1_ = source26_[1]
        source27_ = d_131___mcc_h0_
        if source27_.is_StTrue:
            source28_ = d_132___mcc_h1_
            if source28_.is_StTrue:
                d_133_cond_ = d_132___mcc_h1_
                return d_133_cond_
            elif source28_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_134___mcc_h2_ = source28_.trackedPos
                d_135___mcc_h3_ = source28_.trackedVals
                d_136_cond_ = d_132___mcc_h1_
                return d_136_cond_
        elif source27_.is_StFalse:
            source29_ = d_132___mcc_h1_
            if source29_.is_StTrue:
                return Cond_StFalse()
            elif source29_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_137___mcc_h8_ = source29_.trackedPos
                d_138___mcc_h9_ = source29_.trackedVals
                return Cond_StFalse()
        elif True:
            d_139___mcc_h14_ = source27_.trackedPos
            d_140___mcc_h15_ = source27_.trackedVals
            source30_ = d_132___mcc_h1_
            if source30_.is_StTrue:
                d_141_c1_ = d_131___mcc_h0_
                return d_141_c1_
            elif source30_.is_StFalse:
                return Cond_StFalse()
            elif True:
                d_142___mcc_h22_ = source30_.trackedPos
                d_143___mcc_h23_ = source30_.trackedVals
                d_144_c2_ = d_132___mcc_h1_
                d_145_c1_ = d_131___mcc_h0_
                return default__.Merge(d_145_c1_, d_144_c2_)

    def TrackedPos(self):
        return (self).trackedPos

    def TrackedVals(self):
        return (self).trackedVals

    def TrackedPosAt(self, i):
        return ((self).trackedPos)[i]

    def TrackedValAt(self, i):
        return ((self).trackedVals)[i]

    def Tail(self):
        d_146_dt__update__tmp_h0_ = self
        d_147_dt__update_htrackedVals_h0_ = _dafny.SeqWithoutIsStrInference(((self).trackedVals)[1::])
        d_148_dt__update_htrackedPos_h0_ = _dafny.SeqWithoutIsStrInference(((self).trackedPos)[1::])
        return Cond_StCond(d_148_dt__update_htrackedPos_h0_, d_147_dt__update_htrackedVals_h0_)

    def Add(self, pos, val):
        return self

    def BuildStack(self, r, index):
        _this = self
        while True:
            with _dafny.label():
                if (index) == (len((_this).trackedPos)):
                    return r
                elif (((_this).trackedPos)[index]) < (len(r)):
                    in18_ = _this
                    in19_ = (r).set(((_this).trackedPos)[index], StackElement.StackElem_Value(((_this).trackedVals)[index]))
                    in20_ = (index) + (1)
                    _this = in18_
                    
                    r = in19_
                    index = in20_
                    raise _dafny.TailCall()
                elif True:
                    d_149_suf_ = _dafny.SeqWithoutIsStrInference([StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) for d_150___v2_ in range((((_this).trackedPos)[index]) - (len(r)))])
                    in21_ = _this
                    in22_ = ((r) + (d_149_suf_)) + (_dafny.SeqWithoutIsStrInference([StackElement.StackElem_Value(((_this).trackedVals)[index])]))
                    in23_ = (index) + (1)
                    _this = in21_
                    
                    r = in22_
                    index = in23_
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

