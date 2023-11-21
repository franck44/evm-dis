import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes
import SeqOfSets
import PartitionMod
import Automata

# Module: Minimiser

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Minimise(ap):
        while True:
            with _dafny.label():
                d_35_p1_ = (ap).SplitFrom(0)
                if (len(((d_35_p1_).p).elem)) == (len(((ap).p).elem)):
                    return d_35_p1_
                elif True:
                    in31_ = d_35_p1_
                    ap = in31_
                    raise _dafny.TailCall()
                break


class ValidPair:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Pair_Pair(Automata.Auto_Auto(1, _dafny.Map({})), PartitionMod.Partition_Partition(1, _dafny.SeqWithoutIsStrInference([_dafny.Set({0})])))

class Pair:
    @classmethod
    def default(cls, ):
        return lambda: Pair_Pair(Automata.ValidAuto.default(), PartitionMod.ValidPartition.default())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Pair(self) -> bool:
        return isinstance(self, Pair_Pair)
    def IsValid(self):
        return (((self).a).numStates) == (((self).p).n)

    def ClassSucc(self, x):
        def lambda8_(source0_):
            if source0_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_37___mcc_h0_ = source0_.v
                def iife1_(_pat_let1_0):
                    def iife2_(d_38_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_38_n_, 0))
                    return iife2_(_pat_let1_0)
                return iife1_(d_37___mcc_h0_)

        d_36_s1_ = lambda8_(((self).a).Succ(x, False))
        def lambda9_(source1_):
            if source1_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_40___mcc_h1_ = source1_.v
                def iife3_(_pat_let2_0):
                    def iife4_(d_41_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_41_n_, 0))
                    return iife4_(_pat_let2_0)
                return iife3_(d_40___mcc_h1_)

        d_39_s2_ = lambda9_(((self).a).Succ(x, True))
        return (d_36_s1_, d_39_s2_)

    def SplitFrom(self, index):
        def lambda10_(d_43_index_):
            def lambda11_(d_44_k_):
                def lambda12_(d_45_k_):
                    def lambda13_(d_46_y_):
                        return ((self).ClassSucc(((self).p).GetClass((SeqOfSets.default__.SetToSequence((((self).p).elem)[d_45_k_]))[0], 0))) == ((self).ClassSucc(d_46_y_))

                    return lambda13_

                return lambda12_(d_44_k_)

            return lambda11_

        d_42_splitterF_ = lambda10_(index)
        d_47_r_ = PartitionMod.default__.SplitAllFrom((self).p, d_42_splitterF_, index)
        def iife5_(_pat_let3_0):
            def iife6_(d_49_dt__update__tmp_h0_):
                def iife7_(_pat_let4_0):
                    def iife8_(d_50_dt__update_hp_h0_):
                        return Pair_Pair((d_49_dt__update__tmp_h0_).a, d_50_dt__update_hp_h0_)
                    return iife8_(_pat_let4_0)
                return iife7_(d_47_r_)
            return iife6_(_pat_let3_0)
        d_48_x_ = iife5_(self)
        return d_48_x_

    def Minimise1(self):
        _this = self
        while True:
            with _dafny.label():
                d_51_p1_ = (_this).SplitFrom(0)
                if (len(((d_51_p1_).p).elem)) == (len(((_this).p).elem)):
                    return d_51_p1_
                elif True:
                    in32_ = d_51_p1_
                    _this = in32_
                    
                    raise _dafny.TailCall()
                break


class Pair_Pair(Pair, NamedTuple('Pair', [('a', Any), ('p', Any)])):
    def __dafnystr__(self) -> str:
        return f'Minimiser.Pair.Pair({_dafny.string_of(self.a)}, {_dafny.string_of(self.p)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Pair_Pair) and self.a == __o.a and self.p == __o.p
    def __hash__(self) -> int:
        return super().__hash__()

