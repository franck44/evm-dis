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
import LinSegments
import Splitter
import SegBuilder
import CFGState
import ProofObject
import PrettyIns
import PrettyPrinters
import Automata
import SeqOfSets

# Module: PartitionMod

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def MakeInit(n):
        def iife7_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, n):
                d_853_q_: int = compr_0_
                if ((0) <= (d_853_q_)) and ((d_853_q_) < (n)):
                    coll0_ = coll0_.union(_dafny.Set([d_853_q_]))
            return _dafny.Set(coll0_)
        d_852_s_ = iife7_()

        return Partition_Partition(n, _dafny.SeqWithoutIsStrInference([d_852_s_]))

    @staticmethod
    def SplitTrueAndFalse(xs, equiv, n):
        d_854___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                d_855_first_ = (SeqOfSets.default__.SetToSequence(xs))[0]
                def iife8_():
                    coll1_ = _dafny.Set()
                    compr_1_: int
                    for compr_1_ in (xs).Elements:
                        d_857_x_: int = compr_1_
                        if ((d_857_x_) in (xs)) and (equiv(d_855_first_, d_857_x_)):
                            coll1_ = coll1_.union(_dafny.Set([d_857_x_]))
                    return _dafny.Set(coll1_)
                d_856_xsTrue_ = iife8_()

                d_858_xsFalse_ = (xs) - (d_856_xsTrue_)
                if (d_858_xsFalse_) == (_dafny.Set({})):
                    return (d_854___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_856_xsTrue_]))
                elif True:
                    d_854___accumulator_ = (d_854___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_856_xsTrue_]))
                    in119_ = d_858_xsFalse_
                    in120_ = equiv
                    in121_ = n
                    xs = in119_
                    equiv = in120_
                    n = in121_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SplitAllClasses(xs, equiv, n):
        return _dafny.SeqWithoutIsStrInference([default__.SplitTrueAndFalse((xs)[d_859_i_], equiv, n) for d_859_i_ in range(len(xs))])

    @staticmethod
    def PrintPartition(p):
        hi3_ = len((p).elem)
        for d_860_k_ in range(0, hi3_):
            d_861_setToSeq_: _dafny.Seq
            d_861_setToSeq_ = SeqOfSets.default__.SetToSequence(((p).elem)[d_860_k_])
            _dafny.print(_dafny.string_of(d_861_setToSeq_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))


class ValidPartition:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.MakeInit(1)

class Partition:
    @classmethod
    def default(cls, ):
        return lambda: Partition_Partition(int(0), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Partition(self) -> bool:
        return isinstance(self, Partition_Partition)
    def SplitIn2(self, f):
        def iife9_():
            coll2_ = _dafny.Set()
            compr_2_: int
            for compr_2_ in (SeqOfSets.default__.SetU((self).elem)).Elements:
                d_863_q_: int = compr_2_
                if ((d_863_q_) in (SeqOfSets.default__.SetU((self).elem))) and (f(d_863_q_)):
                    coll2_ = coll2_.union(_dafny.Set([d_863_q_]))
            return _dafny.Set(coll2_)
        d_862_sTrue_ = iife9_()

        d_864_sFalse_ = (SeqOfSets.default__.SetU((self).elem)) - (d_862_sTrue_)
        d_865_d_ = ((_dafny.SeqWithoutIsStrInference([d_862_sTrue_]) if (d_862_sTrue_) != (_dafny.Set({})) else _dafny.SeqWithoutIsStrInference([]))) + ((_dafny.SeqWithoutIsStrInference([d_864_sFalse_]) if (d_864_sFalse_) != (_dafny.Set({})) else _dafny.SeqWithoutIsStrInference([])))
        def iife10_(_pat_let4_0):
            def iife11_(d_867_dt__update__tmp_h0_):
                def iife12_(_pat_let5_0):
                    def iife13_(d_868_dt__update_helem_h0_):
                        return Partition_Partition((d_867_dt__update__tmp_h0_).n, d_868_dt__update_helem_h0_)
                    return iife13_(_pat_let5_0)
                return iife12_(d_865_d_)
            return iife11_(_pat_let4_0)
        d_866_e_ = iife10_(self)
        return d_866_e_

    def ComputeFinest(self, equiv):
        d_869_k_ = default__.SplitTrueAndFalse(SeqOfSets.default__.SetU((self).elem), equiv, (self).n)
        d_870_dt__update__tmp_h0_ = self
        d_871_dt__update_helem_h0_ = d_869_k_
        return Partition_Partition((d_870_dt__update__tmp_h0_).n, d_871_dt__update_helem_h0_)

    def RefineAll(self, equiv):
        d_872_k_ = default__.SplitAllClasses((self).elem, equiv, (self).n)
        d_873_d_ = MiscTypes.default__.Flatten(d_872_k_)
        def iife14_(_pat_let6_0):
            def iife15_(d_875_dt__update__tmp_h0_):
                def iife16_(_pat_let7_0):
                    def iife17_(d_876_dt__update_helem_h0_):
                        return Partition_Partition((d_875_dt__update__tmp_h0_).n, d_876_dt__update_helem_h0_)
                    return iife17_(_pat_let7_0)
                return iife16_(d_873_d_)
            return iife15_(_pat_let6_0)
        d_874_e_ = iife14_(self)
        return d_874_e_

    def GetClass(self, x, index):
        _this = self
        while True:
            with _dafny.label():
                if (x) in (((_this).elem)[index]):
                    return index
                elif True:
                    in122_ = _this
                    in123_ = x
                    in124_ = (index) + (1)
                    _this = in122_
                    
                    x = in123_
                    index = in124_
                    raise _dafny.TailCall()
                break

    def GetClassRepOf(self, x):
        d_877_c_ = (self).GetClass(x, 0)
        return (SeqOfSets.default__.SetToSequence(((self).elem)[d_877_c_]))[0]

    def GetClassRepOfSeqs(self, xs):
        d_878___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_878___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_878___accumulator_ = (d_878___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_this).GetClassRepOf((xs)[0])]))
                    in125_ = _this
                    in126_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    _this = in125_
                    
                    xs = in126_
                    raise _dafny.TailCall()
                break


class Partition_Partition(Partition, NamedTuple('Partition', [('n', Any), ('elem', Any)])):
    def __dafnystr__(self) -> str:
        return f'PartitionMod.Partition.Partition({_dafny.string_of(self.n)}, {_dafny.string_of(self.elem)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Partition_Partition) and self.n == __o.n and self.elem == __o.elem
    def __hash__(self) -> int:
        return super().__hash__()

