import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes
import SeqOfSets

# Module: PartitionMod

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def RemoveEmpty(p, k):
        d_14_p1_ = Partition_Partition((p).n, (_dafny.SeqWithoutIsStrInference(((p).elem)[:k:])) + (_dafny.SeqWithoutIsStrInference(((p).elem)[(k) + (1)::])))
        return d_14_p1_

    @staticmethod
    def SplitAllFrom(p, f, index):
        while True:
            with _dafny.label():
                if (len((p).elem)) == (index):
                    return p
                elif True:
                    d_15_p1_ = (p).SplitAt(f(index), index)
                    def lambda1_(d_17_f_, d_18_p1_, d_19_p_, d_20_index_):
                        def lambda2_(d_21_x_):
                            return d_17_f_((d_21_x_) - ((len((d_18_p1_).elem)) - (len((d_19_p_).elem))))

                        return lambda2_

                    d_16_f_k_ = lambda1_(f, d_15_p1_, p, index)
                    in22_ = d_15_p1_
                    in23_ = d_16_f_k_
                    in24_ = (((index) + (1)) + (len((d_15_p1_).elem))) - (len((p).elem))
                    p = in22_
                    f = in23_
                    index = in24_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintPartition(p):
        hi0_ = len((p).elem)
        for d_22_k_ in range(0, hi0_):
            d_23_setToSeq_: _dafny.Seq
            d_23_setToSeq_ = SeqOfSets.default__.SetToSequence(((p).elem)[d_22_k_])
            _dafny.print(_dafny.string_of(d_23_setToSeq_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))


class ValidPartition:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Partition_Partition(1, _dafny.SeqWithoutIsStrInference([_dafny.Set({0})]))

class Partition:
    @classmethod
    def default(cls, ):
        return lambda: Partition_Partition(int(0), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Partition(self) -> bool:
        return isinstance(self, Partition_Partition)
    def SplitAllFrom2(self, f, index):
        _this = self
        while True:
            with _dafny.label():
                if (len((_this).elem)) == (index):
                    return _this
                elif True:
                    d_24_p1_ = (_this).SplitAt(f(index), index)
                    def lambda3_(d_26_f_, d_27_p1_, d_28_index_):
                        def lambda4_(d_29_x_):
                            return d_26_f_((d_29_x_) - ((len((d_27_p1_).elem)) - (len((_this).elem))))

                        return lambda4_

                    d_25_f_k_ = lambda3_(f, d_24_p1_, index)
                    in25_ = d_24_p1_
                    in26_ = d_25_f_k_
                    in27_ = (((index) + (1)) + (len((d_24_p1_).elem))) - (len((_this).elem))
                    _this = in25_
                    
                    f = in26_
                    index = in27_
                    raise _dafny.TailCall()
                break

    def SplitAt(self, f, index):
        d_30_r_ = SeqOfSets.default__.SplitSet(((self).elem)[index], f)
        d_31_newP_ = ((_dafny.SeqWithoutIsStrInference(((self).elem)[:index:])) + (_dafny.SeqWithoutIsStrInference([(d_30_r_)[0], (d_30_r_)[1]]))) + (_dafny.SeqWithoutIsStrInference(((self).elem)[(index) + (1)::]))
        if ((d_30_r_)[0]) == (_dafny.Set({})):
            return default__.RemoveEmpty(Partition_Partition((self).n, d_31_newP_), index)
        elif ((d_30_r_)[1]) == (_dafny.Set({})):
            return default__.RemoveEmpty(Partition_Partition((self).n, d_31_newP_), (index) + (1))
        elif True:
            return Partition_Partition((self).n, d_31_newP_)

    def GetClass(self, x, index):
        _this = self
        while True:
            with _dafny.label():
                if (x) in (((_this).elem)[index]):
                    return index
                elif True:
                    in28_ = _this
                    in29_ = x
                    in30_ = (index) + (1)
                    _this = in28_
                    
                    x = in29_
                    index = in30_
                    raise _dafny.TailCall()
                break

    def Equiv(self, x, y):
        return ((self).GetClass(x, 0)) == ((self).GetClass(y, 0))

    def Refines(self, p):
        def lambda5_(forall_var_1_):
            def lambda6_(forall_var_2_):
                d_33_x_k_: int = forall_var_2_
                return not ((((0) <= (d_32_x_)) and ((d_32_x_) < (d_33_x_k_))) and ((d_33_x_k_) < ((self).n))) or (not ((self).Equiv(d_32_x_, d_33_x_k_)) or ((p).Equiv(d_32_x_, d_33_x_k_)))

            d_32_x_: int = forall_var_1_
            return _dafny.quantifier(_dafny.IntegerRange((d_32_x_) + (1), (self).n), True, lambda6_)

        return _dafny.quantifier(_dafny.IntegerRange(0, (self).n), True, lambda5_)


class Partition_Partition(Partition, NamedTuple('Partition', [('n', Any), ('elem', Any)])):
    def __dafnystr__(self) -> str:
        return f'PartitionMod.Partition.Partition({_dafny.string_of(self.n)}, {_dafny.string_of(self.elem)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Partition_Partition) and self.n == __o.n and self.elem == __o.elem
    def __hash__(self) -> int:
        return super().__hash__()

