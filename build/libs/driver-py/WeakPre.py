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

# Module: WeakPre

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def StackToCond(xs):
        d_0_r_ = default__.StackToCondHelper(xs, (_dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([])), 0)
        if (len((d_0_r_)[0])) == (0):
            return Cond_StTrue()
        elif True:
            return Cond_StCond((d_0_r_)[0], (d_0_r_)[1])

    @staticmethod
    def StackToCondHelper(xs, c, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return c
                elif ((xs)[index]).is_Value:
                    d_0_c_k_ = (((c)[0]) + (_dafny.SeqWithoutIsStrInference([index])), ((c)[1]) + (_dafny.SeqWithoutIsStrInference([((xs)[index]).v])))
                    in0_ = xs
                    in1_ = d_0_c_k_
                    in2_ = (index) + (1)
                    xs = in0_
                    c = in1_
                    index = in2_
                    raise _dafny.TailCall()
                elif True:
                    in3_ = xs
                    in4_ = c
                    in5_ = (index) + (1)
                    xs = in3_
                    c = in4_
                    index = in5_
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
                        d_0_i_ = default__.FindVal(((c2).trackedPos)[0], (c1).trackedPos, 0)
                        if (((c1).trackedVals)[d_0_i_]) == (((c2).trackedVals)[0]):
                            return c1
                        elif True:
                            return Cond_StFalse()
                    elif True:
                        return Cond_StCond(((c1).trackedPos) + (_dafny.SeqWithoutIsStrInference([((c2).trackedPos)[0]])), ((c1).trackedVals) + (_dafny.SeqWithoutIsStrInference([((c2).trackedVals)[0]])))
                elif True:
                    if (((c2).trackedPos)[0]) in ((c1).trackedPos):
                        in0_ = c1
                        in1_ = Cond_StCond(_dafny.SeqWithoutIsStrInference(((c2).trackedPos)[1::]), _dafny.SeqWithoutIsStrInference(((c2).trackedVals)[1::]))
                        c1 = in0_
                        c2 = in1_
                        raise _dafny.TailCall()
                    elif True:
                        d_1_p_ = ((c1).trackedPos) + (_dafny.SeqWithoutIsStrInference([((c2).trackedPos)[0]]))
                        d_2_v_ = ((c1).trackedVals) + (_dafny.SeqWithoutIsStrInference([((c2).trackedVals)[0]]))
                        in2_ = Cond_StCond(d_1_p_, d_2_v_)
                        in3_ = Cond_StCond(_dafny.SeqWithoutIsStrInference(((c2).trackedPos)[1::]), _dafny.SeqWithoutIsStrInference(((c2).trackedVals)[1::]))
                        c1 = in2_
                        c2 = in3_
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
                    in0_ = x
                    in1_ = xs
                    in2_ = (index) + (1)
                    x = in0_
                    xs = in1_
                    index = in2_
                    raise _dafny.TailCall()
                break


class ValidCond:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Cond_StCond(_dafny.SeqWithoutIsStrInference([1]), _dafny.SeqWithoutIsStrInference([0]))
    def _Is(source__):
        d_0_c_: Cond = source__
        return (d_0_c_).IsValid()

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
                d_1_k_k_: int = forall_var_1_
                return not ((((0) <= (d_0_k_)) and ((d_0_k_) < (d_1_k_k_))) and ((d_1_k_k_) < (len((self).trackedPos)))) or ((((self).trackedPos)[d_0_k_]) != (((self).trackedPos)[d_1_k_k_]))

            d_0_k_: int = forall_var_0_
            return _dafny.quantifier(_dafny.IntegerRange((d_0_k_) + (1), len((self).trackedPos)), True, lambda1_)

        return not ((self).is_StCond) or ((((len((self).trackedPos)) == (len((self).trackedVals))) and ((len((self).trackedVals)) > (0))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).trackedPos)), True, lambda0_)))

    def Size(self):
        if (self).is_StCond:
            return len((self).trackedPos)
        elif True:
            return 0

    def And(self, c):
        source0_ = (self, c)
        if True:
            d_00_ = source0_[0]
            if d_00_.is_StFalse:
                return Cond_StFalse()
        if True:
            d_10_ = source0_[1]
            if d_10_.is_StFalse:
                return Cond_StFalse()
        if True:
            d_01_ = source0_[0]
            if d_01_.is_StTrue:
                d_0_cond_ = source0_[1]
                return d_0_cond_
        if True:
            d_1_c1_ = source0_[0]
            d_11_ = source0_[1]
            if d_11_.is_StTrue:
                return d_1_c1_
        if True:
            d_2_c1_ = source0_[0]
            d_3_c2_ = source0_[1]
            return default__.Merge(d_2_c1_, d_3_c2_)

    def TrackedPos(self):
        return (self).trackedPos

    def TrackedVals(self):
        return (self).trackedVals

    def TrackedPosAt(self, i):
        return ((self).trackedPos)[i]

    def TrackedValAt(self, i):
        return ((self).trackedVals)[i]

    def Tail(self):
        d_0_dt__update__tmp_h0_ = self
        d_1_dt__update_htrackedVals_h0_ = _dafny.SeqWithoutIsStrInference(((self).trackedVals)[1::])
        d_2_dt__update_htrackedPos_h0_ = _dafny.SeqWithoutIsStrInference(((self).trackedPos)[1::])
        return Cond_StCond(d_2_dt__update_htrackedPos_h0_, d_1_dt__update_htrackedVals_h0_)

    def Add(self, pos, val):
        return self

    def BuildStack(self, r, index):
        _this = self
        while True:
            with _dafny.label():
                if (index) == (len((_this).trackedPos)):
                    return r
                elif (((_this).trackedPos)[index]) < (len(r)):
                    in0_ = _this
                    in1_ = (r).set(((_this).trackedPos)[index], StackElement.StackElem_Value(((_this).trackedVals)[index]))
                    in2_ = (index) + (1)
                    _this = in0_
                    
                    r = in1_
                    index = in2_
                    raise _dafny.TailCall()
                elif True:
                    d_0_suf_ = _dafny.SeqWithoutIsStrInference([StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) for d_1___v2_ in range((((_this).trackedPos)[index]) - (len(r)))])
                    in3_ = _this
                    in4_ = ((r) + (d_0_suf_)) + (_dafny.SeqWithoutIsStrInference([StackElement.StackElem_Value(((_this).trackedVals)[index])]))
                    in5_ = (index) + (1)
                    _this = in3_
                    
                    r = in4_
                    index = in5_
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

