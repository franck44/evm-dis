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
import ProofObject
import PrettyIns
import PrettyPrinters
import CFGState
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
                d_827_q_: int = compr_0_
                if ((0) <= (d_827_q_)) and ((d_827_q_) < (n)):
                    coll0_ = coll0_.union(_dafny.Set([d_827_q_]))
            return _dafny.Set(coll0_)
        d_826_s_ = iife7_()

        return Partition_Partition(n, _dafny.SeqWithoutIsStrInference([d_826_s_]))

    @staticmethod
    def SplitTrueAndFalse(xs, equiv, n):
        d_828___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                d_829_first_ = (SeqOfSets.default__.SetToSequence(xs))[0]
                def iife8_():
                    coll1_ = _dafny.Set()
                    compr_1_: int
                    for compr_1_ in (xs).Elements:
                        d_831_x_: int = compr_1_
                        if ((d_831_x_) in (xs)) and (equiv(d_829_first_, d_831_x_)):
                            coll1_ = coll1_.union(_dafny.Set([d_831_x_]))
                    return _dafny.Set(coll1_)
                d_830_xsTrue_ = iife8_()

                d_832_xsFalse_ = (xs) - (d_830_xsTrue_)
                if (d_832_xsFalse_) == (_dafny.Set({})):
                    return (d_828___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_830_xsTrue_]))
                elif True:
                    d_828___accumulator_ = (d_828___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_830_xsTrue_]))
                    in104_ = d_832_xsFalse_
                    in105_ = equiv
                    in106_ = n
                    xs = in104_
                    equiv = in105_
                    n = in106_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SplitAllClasses(xs, equiv, n):
        return _dafny.SeqWithoutIsStrInference([default__.SplitTrueAndFalse((xs)[d_833_i_], equiv, n) for d_833_i_ in range(len(xs))])

    @staticmethod
    def PrintPartition(p):
        hi3_ = len((p).elem)
        for d_834_k_ in range(0, hi3_):
            d_835_setToSeq_: _dafny.Seq
            d_835_setToSeq_ = SeqOfSets.default__.SetToSequence(((p).elem)[d_834_k_])
            _dafny.print(_dafny.string_of(d_835_setToSeq_))
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
                d_837_q_: int = compr_2_
                if ((d_837_q_) in (SeqOfSets.default__.SetU((self).elem))) and (f(d_837_q_)):
                    coll2_ = coll2_.union(_dafny.Set([d_837_q_]))
            return _dafny.Set(coll2_)
        d_836_sTrue_ = iife9_()

        d_838_sFalse_ = (SeqOfSets.default__.SetU((self).elem)) - (d_836_sTrue_)
        d_839_d_ = ((_dafny.SeqWithoutIsStrInference([d_836_sTrue_]) if (d_836_sTrue_) != (_dafny.Set({})) else _dafny.SeqWithoutIsStrInference([]))) + ((_dafny.SeqWithoutIsStrInference([d_838_sFalse_]) if (d_838_sFalse_) != (_dafny.Set({})) else _dafny.SeqWithoutIsStrInference([])))
        def iife10_(_pat_let4_0):
            def iife11_(d_841_dt__update__tmp_h0_):
                def iife12_(_pat_let5_0):
                    def iife13_(d_842_dt__update_helem_h0_):
                        return Partition_Partition((d_841_dt__update__tmp_h0_).n, d_842_dt__update_helem_h0_)
                    return iife13_(_pat_let5_0)
                return iife12_(d_839_d_)
            return iife11_(_pat_let4_0)
        d_840_e_ = iife10_(self)
        return d_840_e_

    def ComputeFinest(self, equiv):
        d_843_k_ = default__.SplitTrueAndFalse(SeqOfSets.default__.SetU((self).elem), equiv, (self).n)
        d_844_dt__update__tmp_h0_ = self
        d_845_dt__update_helem_h0_ = d_843_k_
        return Partition_Partition((d_844_dt__update__tmp_h0_).n, d_845_dt__update_helem_h0_)

    def RefineAll(self, equiv):
        d_846_k_ = default__.SplitAllClasses((self).elem, equiv, (self).n)
        d_847_d_ = MiscTypes.default__.Flatten(d_846_k_)
        def iife14_(_pat_let6_0):
            def iife15_(d_849_dt__update__tmp_h0_):
                def iife16_(_pat_let7_0):
                    def iife17_(d_850_dt__update_helem_h0_):
                        return Partition_Partition((d_849_dt__update__tmp_h0_).n, d_850_dt__update_helem_h0_)
                    return iife17_(_pat_let7_0)
                return iife16_(d_847_d_)
            return iife15_(_pat_let6_0)
        d_848_e_ = iife14_(self)
        return d_848_e_

    def GetClass(self, x, index):
        _this = self
        while True:
            with _dafny.label():
                if (x) in (((_this).elem)[index]):
                    return index
                elif True:
                    in107_ = _this
                    in108_ = x
                    in109_ = (index) + (1)
                    _this = in107_
                    
                    x = in108_
                    index = in109_
                    raise _dafny.TailCall()
                break

    def GetClassRepOf(self, x):
        d_851_c_ = (self).GetClass(x, 0)
        return (SeqOfSets.default__.SetToSequence(((self).elem)[d_851_c_]))[0]

    def GetClassRepOfSeqs(self, xs):
        d_852___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_852___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_852___accumulator_ = (d_852___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_this).GetClassRepOf((xs)[0])]))
                    in110_ = _this
                    in111_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    _this = in110_
                    
                    xs = in111_
                    raise _dafny.TailCall()
                break


class Partition_Partition(Partition, NamedTuple('Partition', [('n', Any), ('elem', Any)])):
    def __dafnystr__(self) -> str:
        return f'PartitionMod.Partition.Partition({_dafny.string_of(self.n)}, {_dafny.string_of(self.elem)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Partition_Partition) and self.n == __o.n and self.elem == __o.elem
    def __hash__(self) -> int:
        return super().__hash__()

