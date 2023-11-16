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
import State
import WeakPre
import Instructions
import BinaryDecoder
import LinSegments
import Splitter
import SegBuilder
import ProofObject
import PrettyIns
import PrettyPrinters
import ProofObjectBuilder
import ArgParser
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
                d_630_p1_ = (ap).SplitFrom()
                if (len(((d_630_p1_).p).elem)) == (len(((ap).p).elem)):
                    return d_630_p1_
                elif True:
                    in90_ = d_630_p1_
                    ap = in90_
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

    def Auto(self):
        return (self).a

    def Parts(self):
        return (self).p

    def ClassSucc(self, x):
        def lambda27_(source51_):
            if source51_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_632___mcc_h0_ = source51_.v
                def iife4_(_pat_let2_0):
                    def iife5_(d_633_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_633_n_, 0))
                    return iife5_(_pat_let2_0)
                return iife4_(d_632___mcc_h0_)

        d_631_s1_ = lambda27_(((self).a).Succ(x, False))
        def lambda28_(source52_):
            if source52_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_635___mcc_h1_ = source52_.v
                def iife6_(_pat_let3_0):
                    def iife7_(d_636_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_636_n_, 0))
                    return iife7_(_pat_let3_0)
                return iife6_(d_635___mcc_h1_)

        d_634_s2_ = lambda28_(((self).a).Succ(x, True))
        return (d_631_s1_, d_634_s2_)

    def SplitFrom(self):
        def lambda29_(d_638_k_):
            def lambda30_(d_639_k_):
                def lambda31_(d_640_y_):
                    return ((self).ClassSucc((SeqOfSets.default__.SetToSequence((((self).p).elem)[d_639_k_]))[0])) == ((self).ClassSucc(d_640_y_))

                return lambda31_

            return lambda30_(d_638_k_)

        d_637_splitterF_ = lambda29_
        d_641_r_ = PartitionMod.default__.SplitAll((self).p, d_637_splitterF_, 0, len(((self).p).elem))
        d_642_dt__update__tmp_h0_ = self
        d_643_dt__update_hp_h0_ = d_641_r_
        return Pair_Pair((d_642_dt__update__tmp_h0_).a, d_643_dt__update_hp_h0_)

    def GenerateReduced(self, index):
        d_644___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (index) == (len(((_this).p).elem)):
                    return (d_644___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_645_firstElem_ = (SeqOfSets.default__.SetToSequence((((_this).p).elem)[index]))[0]
                    d_646_succs_ = (_this).ClassSucc(d_645_firstElem_)
                    def lambda32_(source53_):
                        d_648___mcc_h0_ = source53_[0]
                        d_649___mcc_h1_ = source53_[1]
                        def lambda33_(source54_):
                            if source54_.is_None:
                                def lambda34_(source55_):
                                    if source55_.is_None:
                                        return _dafny.SeqWithoutIsStrInference([])
                                    elif True:
                                        d_650___mcc_h2_ = source55_.v
                                        def iife8_(_pat_let4_0):
                                            def iife9_(d_651_sTrue_):
                                                return _dafny.SeqWithoutIsStrInference([(d_645_firstElem_, True, (SeqOfSets.default__.SetToSequence((((_this).p).elem)[d_651_sTrue_]))[0])])
                                            return iife9_(_pat_let4_0)
                                        return iife8_(d_650___mcc_h2_)

                                return lambda34_(d_649___mcc_h1_)
                            elif True:
                                d_652___mcc_h3_ = source54_.v
                                def lambda35_(source56_):
                                    if source56_.is_None:
                                        def iife10_(_pat_let5_0):
                                            def iife11_(d_653_sFalse_):
                                                return _dafny.SeqWithoutIsStrInference([(d_645_firstElem_, False, (SeqOfSets.default__.SetToSequence((((_this).p).elem)[d_653_sFalse_]))[0])])
                                            return iife11_(_pat_let5_0)
                                        return iife10_(d_652___mcc_h3_)
                                    elif True:
                                        d_654___mcc_h4_ = source56_.v
                                        def iife12_(_pat_let6_0):
                                            def iife13_(d_655_sTrue_):
                                                def iife14_(_pat_let7_0):
                                                    def iife15_(d_656_sFalse_):
                                                        return _dafny.SeqWithoutIsStrInference([(d_645_firstElem_, False, (SeqOfSets.default__.SetToSequence((((_this).p).elem)[d_656_sFalse_]))[0]), (d_645_firstElem_, True, (SeqOfSets.default__.SetToSequence((((_this).p).elem)[d_655_sTrue_]))[0])])
                                                    return iife15_(_pat_let7_0)
                                                return iife14_(d_652___mcc_h3_)
                                            return iife13_(_pat_let6_0)
                                        return iife12_(d_654___mcc_h4_)

                                return lambda35_(d_649___mcc_h1_)

                        return lambda33_(d_648___mcc_h0_)

                    d_647_newEdges_ = lambda32_(((d_646_succs_)[0], (d_646_succs_)[1]))
                    d_644___accumulator_ = (d_644___accumulator_) + (d_647_newEdges_)
                    in91_ = _this
                    in92_ = (index) + (1)
                    _this = in91_
                    
                    index = in92_
                    raise _dafny.TailCall()
                break

    def Minimise1(self):
        _this = self
        while True:
            with _dafny.label():
                d_657_p1_ = (_this).SplitFrom()
                if (len(((d_657_p1_).p).elem)) == (len(((_this).p).elem)):
                    return d_657_p1_
                elif True:
                    in93_ = d_657_p1_
                    _this = in93_
                    
                    raise _dafny.TailCall()
                break


class Pair_Pair(Pair, NamedTuple('Pair', [('a', Any), ('p', Any)])):
    def __dafnystr__(self) -> str:
        return f'Minimiser.Pair.Pair({_dafny.string_of(self.a)}, {_dafny.string_of(self.p)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Pair_Pair) and self.a == __o.a and self.p == __o.p
    def __hash__(self) -> int:
        return super().__hash__()

