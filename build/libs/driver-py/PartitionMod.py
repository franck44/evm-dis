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
import LinSegments as LinSegments
import Splitter as Splitter
import SegBuilder as SegBuilder
import CFGState as CFGState
import ProofObject as ProofObject
import PrettyIns as PrettyIns
import PrettyPrinters as PrettyPrinters
import Automata as Automata
import SeqOfSets as SeqOfSets

# Module: PartitionMod

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def MakeInit(n):
        def iife0_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, n):
                d_1_q_: int = compr_0_
                if ((0) <= (d_1_q_)) and ((d_1_q_) < (n)):
                    coll0_ = coll0_.union(_dafny.Set([d_1_q_]))
            return _dafny.Set(coll0_)
        d_0_s_ = iife0_()

        return Partition_Partition(n, _dafny.SeqWithoutIsStrInference([d_0_s_]))

    @staticmethod
    def SplitTrueAndFalse(xs, equiv, n):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                d_1_first_ = (SeqOfSets.default__.SetToSequence(xs))[0]
                def iife0_():
                    coll0_ = _dafny.Set()
                    compr_0_: int
                    for compr_0_ in (xs).Elements:
                        d_3_x_: int = compr_0_
                        if System_.nat._Is(d_3_x_):
                            if ((d_3_x_) in (xs)) and (equiv(d_1_first_, d_3_x_)):
                                coll0_ = coll0_.union(_dafny.Set([d_3_x_]))
                    return _dafny.Set(coll0_)
                d_2_xsTrue_ = iife0_()

                d_4_xsFalse_ = (xs) - (d_2_xsTrue_)
                if (d_4_xsFalse_) == (_dafny.Set({})):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_2_xsTrue_]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_2_xsTrue_]))
                    in0_ = d_4_xsFalse_
                    in1_ = equiv
                    in2_ = n
                    xs = in0_
                    equiv = in1_
                    n = in2_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SplitAllClasses(xs, equiv, n):
        return _dafny.SeqWithoutIsStrInference([default__.SplitTrueAndFalse((xs)[d_0_i_], equiv, n) for d_0_i_ in range(len(xs))])

    @staticmethod
    def PrintPartition(p):
        hi0_ = len((p).elem)
        for d_0_k_ in range(0, hi0_):
            d_1_setToSeq_: _dafny.Seq
            d_1_setToSeq_ = SeqOfSets.default__.SetToSequence(((p).elem)[d_0_k_])
            _dafny.print(_dafny.string_of(d_1_setToSeq_))
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
        def iife0_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in (SeqOfSets.default__.SetU((self).elem)).Elements:
                d_1_q_: int = compr_0_
                if System_.nat._Is(d_1_q_):
                    if ((d_1_q_) in (SeqOfSets.default__.SetU((self).elem))) and (f(d_1_q_)):
                        coll0_ = coll0_.union(_dafny.Set([d_1_q_]))
            return _dafny.Set(coll0_)
        d_0_sTrue_ = iife0_()

        d_2_sFalse_ = (SeqOfSets.default__.SetU((self).elem)) - (d_0_sTrue_)
        d_3_d_ = ((_dafny.SeqWithoutIsStrInference([d_0_sTrue_]) if (d_0_sTrue_) != (_dafny.Set({})) else _dafny.SeqWithoutIsStrInference([]))) + ((_dafny.SeqWithoutIsStrInference([d_2_sFalse_]) if (d_2_sFalse_) != (_dafny.Set({})) else _dafny.SeqWithoutIsStrInference([])))
        def iife1_(_pat_let4_0):
            def iife2_(d_5_dt__update__tmp_h0_):
                def iife3_(_pat_let5_0):
                    def iife4_(d_6_dt__update_helem_h0_):
                        return Partition_Partition((d_5_dt__update__tmp_h0_).n, d_6_dt__update_helem_h0_)
                    return iife4_(_pat_let5_0)
                return iife3_(d_3_d_)
            return iife2_(_pat_let4_0)
        d_4_e_ = iife1_(self)
        return d_4_e_

    def ComputeFinest(self, equiv):
        d_0_k_ = default__.SplitTrueAndFalse(SeqOfSets.default__.SetU((self).elem), equiv, (self).n)
        d_1_dt__update__tmp_h0_ = self
        d_2_dt__update_helem_h0_ = d_0_k_
        return Partition_Partition((d_1_dt__update__tmp_h0_).n, d_2_dt__update_helem_h0_)

    def RefineAll(self, equiv):
        d_0_k_ = default__.SplitAllClasses((self).elem, equiv, (self).n)
        d_1_d_ = MiscTypes.default__.Flatten(d_0_k_)
        def iife0_(_pat_let6_0):
            def iife1_(d_3_dt__update__tmp_h0_):
                def iife2_(_pat_let7_0):
                    def iife3_(d_4_dt__update_helem_h0_):
                        return Partition_Partition((d_3_dt__update__tmp_h0_).n, d_4_dt__update_helem_h0_)
                    return iife3_(_pat_let7_0)
                return iife2_(d_1_d_)
            return iife1_(_pat_let6_0)
        d_2_e_ = iife0_(self)
        return d_2_e_

    def GetClass(self, x, index):
        _this = self
        while True:
            with _dafny.label():
                if (x) in (((_this).elem)[index]):
                    return index
                elif True:
                    in0_ = _this
                    in1_ = x
                    in2_ = (index) + (1)
                    _this = in0_
                    
                    x = in1_
                    index = in2_
                    raise _dafny.TailCall()
                break

    def GetClassRepOf(self, x):
        d_0_c_ = (self).GetClass(x, 0)
        return (SeqOfSets.default__.SetToSequence(((self).elem)[d_0_c_]))[0]

    def GetClassRepOfSeqs(self, xs):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_this).GetClassRepOf((xs)[0])]))
                    in0_ = _this
                    in1_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    _this = in0_
                    
                    xs = in1_
                    raise _dafny.TailCall()
                break


class Partition_Partition(Partition, NamedTuple('Partition', [('n', Any), ('elem', Any)])):
    def __dafnystr__(self) -> str:
        return f'PartitionMod.Partition.Partition({_dafny.string_of(self.n)}, {_dafny.string_of(self.elem)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Partition_Partition) and self.n == __o.n and self.elem == __o.elem
    def __hash__(self) -> int:
        return super().__hash__()

