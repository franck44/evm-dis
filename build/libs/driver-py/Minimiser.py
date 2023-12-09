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
import EVMObject
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
        d_854_p1_ = (ap).SplitFrom()
        if (len(((d_854_p1_).p).elem)) == (len(((ap).p).elem)):
            return d_854_p1_
        elif True:
            return default__.Minimise(d_854_p1_)


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
        def lambda48_(source58_):
            if source58_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_856___mcc_h0_ = source58_.v
                def iife2_(_pat_let1_0):
                    def iife3_(d_857_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_857_n_, 0))
                    return iife3_(_pat_let1_0)
                return iife2_(d_856___mcc_h0_)

        d_855_s1_ = lambda48_(((self).a).Succ(x, False))
        def lambda49_(source59_):
            if source59_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_859___mcc_h1_ = source59_.v
                def iife4_(_pat_let2_0):
                    def iife5_(d_860_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_860_n_, 0))
                    return iife5_(_pat_let2_0)
                return iife4_(d_859___mcc_h1_)

        d_858_s2_ = lambda49_(((self).a).Succ(x, True))
        return (d_855_s1_, d_858_s2_)

    def SplitFrom(self):
        def lambda50_(d_862_k_):
            def lambda51_(d_863_k_):
                def lambda52_(d_864_y_):
                    return ((self).ClassSucc((SeqOfSets.default__.SetToSequence((((self).p).elem)[d_863_k_]))[0])) == ((self).ClassSucc(d_864_y_))

                return lambda52_

            return lambda51_(d_862_k_)

        d_861_splitterF_ = lambda50_
        d_865_r_ = PartitionMod.default__.SplitAll((self).p, d_861_splitterF_, 0, len(((self).p).elem))
        d_866_dt__update__tmp_h0_ = self
        d_867_dt__update_hp_h0_ = d_865_r_
        return Pair_Pair((d_866_dt__update__tmp_h0_).a, d_867_dt__update_hp_h0_)

    def GenerateReducedTailRec(self, index, acc):
        if (index) == (len(((self).p).elem)):
            return acc
        elif True:
            d_868_firstElem_ = (SeqOfSets.default__.SetToSequence((((self).p).elem)[index]))[0]
            d_869_succs_ = (self).ClassSucc(d_868_firstElem_)
            def lambda53_(source60_):
                d_871___mcc_h0_ = source60_[0]
                d_872___mcc_h1_ = source60_[1]
                def lambda54_(source61_):
                    if source61_.is_None:
                        def lambda55_(source62_):
                            if source62_.is_None:
                                return _dafny.SeqWithoutIsStrInference([])
                            elif True:
                                d_873___mcc_h2_ = source62_.v
                                def iife6_(_pat_let3_0):
                                    def iife7_(d_874_sTrue_):
                                        return _dafny.SeqWithoutIsStrInference([(d_868_firstElem_, True, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_874_sTrue_]))[0])])
                                    return iife7_(_pat_let3_0)
                                return iife6_(d_873___mcc_h2_)

                        return lambda55_(d_872___mcc_h1_)
                    elif True:
                        d_875___mcc_h3_ = source61_.v
                        def lambda56_(source63_):
                            if source63_.is_None:
                                def iife8_(_pat_let4_0):
                                    def iife9_(d_876_sFalse_):
                                        return _dafny.SeqWithoutIsStrInference([(d_868_firstElem_, False, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_876_sFalse_]))[0])])
                                    return iife9_(_pat_let4_0)
                                return iife8_(d_875___mcc_h3_)
                            elif True:
                                d_877___mcc_h4_ = source63_.v
                                def iife10_(_pat_let5_0):
                                    def iife11_(d_878_sTrue_):
                                        def iife12_(_pat_let6_0):
                                            def iife13_(d_879_sFalse_):
                                                return _dafny.SeqWithoutIsStrInference([(d_868_firstElem_, False, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_879_sFalse_]))[0]), (d_868_firstElem_, True, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_878_sTrue_]))[0])])
                                            return iife13_(_pat_let6_0)
                                        return iife12_(d_875___mcc_h3_)
                                    return iife11_(_pat_let5_0)
                                return iife10_(d_877___mcc_h4_)

                        return lambda56_(d_872___mcc_h1_)

                return lambda54_(d_871___mcc_h0_)

            d_870_newEdges_ = lambda53_(((d_869_succs_)[0], (d_869_succs_)[1]))
            return (self).GenerateReducedTailRec((index) + (1), (acc) + (d_870_newEdges_))


class Pair_Pair(Pair, NamedTuple('Pair', [('a', Any), ('p', Any)])):
    def __dafnystr__(self) -> str:
        return f'Minimiser.Pair.Pair({_dafny.string_of(self.a)}, {_dafny.string_of(self.p)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Pair_Pair) and self.a == __o.a and self.p == __o.p
    def __hash__(self) -> int:
        return super().__hash__()

