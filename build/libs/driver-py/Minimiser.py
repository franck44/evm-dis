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
        d_833_p1_ = (ap).SplitFrom()
        if (len(((d_833_p1_).p).elem)) == (len(((ap).p).elem)):
            return d_833_p1_
        elif True:
            return default__.Minimise(d_833_p1_)


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
        def lambda42_(source57_):
            if source57_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_835___mcc_h0_ = source57_.v
                def iife4_(_pat_let2_0):
                    def iife5_(d_836_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_836_n_, 0))
                    return iife5_(_pat_let2_0)
                return iife4_(d_835___mcc_h0_)

        d_834_s1_ = lambda42_(((self).a).Succ(x, False))
        def lambda43_(source58_):
            if source58_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_838___mcc_h1_ = source58_.v
                def iife6_(_pat_let3_0):
                    def iife7_(d_839_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_839_n_, 0))
                    return iife7_(_pat_let3_0)
                return iife6_(d_838___mcc_h1_)

        d_837_s2_ = lambda43_(((self).a).Succ(x, True))
        return (d_834_s1_, d_837_s2_)

    def SplitFrom(self):
        def lambda44_(d_841_k_):
            def lambda45_(d_842_k_):
                def lambda46_(d_843_y_):
                    return ((self).ClassSucc((SeqOfSets.default__.SetToSequence((((self).p).elem)[d_842_k_]))[0])) == ((self).ClassSucc(d_843_y_))

                return lambda46_

            return lambda45_(d_841_k_)

        d_840_splitterF_ = lambda44_
        d_844_r_ = PartitionMod.default__.SplitAll((self).p, d_840_splitterF_, 0, len(((self).p).elem))
        d_845_dt__update__tmp_h0_ = self
        d_846_dt__update_hp_h0_ = d_844_r_
        return Pair_Pair((d_845_dt__update__tmp_h0_).a, d_846_dt__update_hp_h0_)

    def GenerateReducedTailRec(self, index, acc):
        if (index) == (len(((self).p).elem)):
            return acc
        elif True:
            d_847_firstElem_ = (SeqOfSets.default__.SetToSequence((((self).p).elem)[index]))[0]
            d_848_succs_ = (self).ClassSucc(d_847_firstElem_)
            def lambda47_(source59_):
                d_850___mcc_h0_ = source59_[0]
                d_851___mcc_h1_ = source59_[1]
                def lambda48_(source60_):
                    if source60_.is_None:
                        def lambda49_(source61_):
                            if source61_.is_None:
                                return _dafny.SeqWithoutIsStrInference([])
                            elif True:
                                d_852___mcc_h2_ = source61_.v
                                def iife8_(_pat_let4_0):
                                    def iife9_(d_853_sTrue_):
                                        return _dafny.SeqWithoutIsStrInference([(d_847_firstElem_, True, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_853_sTrue_]))[0])])
                                    return iife9_(_pat_let4_0)
                                return iife8_(d_852___mcc_h2_)

                        return lambda49_(d_851___mcc_h1_)
                    elif True:
                        d_854___mcc_h3_ = source60_.v
                        def lambda50_(source62_):
                            if source62_.is_None:
                                def iife10_(_pat_let5_0):
                                    def iife11_(d_855_sFalse_):
                                        return _dafny.SeqWithoutIsStrInference([(d_847_firstElem_, False, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_855_sFalse_]))[0])])
                                    return iife11_(_pat_let5_0)
                                return iife10_(d_854___mcc_h3_)
                            elif True:
                                d_856___mcc_h4_ = source62_.v
                                def iife12_(_pat_let6_0):
                                    def iife13_(d_857_sTrue_):
                                        def iife14_(_pat_let7_0):
                                            def iife15_(d_858_sFalse_):
                                                return _dafny.SeqWithoutIsStrInference([(d_847_firstElem_, False, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_858_sFalse_]))[0]), (d_847_firstElem_, True, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_857_sTrue_]))[0])])
                                            return iife15_(_pat_let7_0)
                                        return iife14_(d_854___mcc_h3_)
                                    return iife13_(_pat_let6_0)
                                return iife12_(d_856___mcc_h4_)

                        return lambda50_(d_851___mcc_h1_)

                return lambda48_(d_850___mcc_h0_)

            d_849_newEdges_ = lambda47_(((d_848_succs_)[0], (d_848_succs_)[1]))
            return (self).GenerateReducedTailRec((index) + (1), (acc) + (d_849_newEdges_))


class Pair_Pair(Pair, NamedTuple('Pair', [('a', Any), ('p', Any)])):
    def __dafnystr__(self) -> str:
        return f'Minimiser.Pair.Pair({_dafny.string_of(self.a)}, {_dafny.string_of(self.p)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Pair_Pair) and self.a == __o.a and self.p == __o.p
    def __hash__(self) -> int:
        return super().__hash__()

