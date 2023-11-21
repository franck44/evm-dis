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
import WeakPre
import State
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
        d_685_p1_ = (ap).SplitFrom()
        if (len(((d_685_p1_).p).elem)) == (len(((ap).p).elem)):
            return d_685_p1_
        elif True:
            return default__.Minimise(d_685_p1_)


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
        def lambda27_(source57_):
            if source57_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_687___mcc_h0_ = source57_.v
                def iife4_(_pat_let2_0):
                    def iife5_(d_688_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_688_n_, 0))
                    return iife5_(_pat_let2_0)
                return iife4_(d_687___mcc_h0_)

        d_686_s1_ = lambda27_(((self).a).Succ(x, False))
        def lambda28_(source58_):
            if source58_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_690___mcc_h1_ = source58_.v
                def iife6_(_pat_let3_0):
                    def iife7_(d_691_n_):
                        return MiscTypes.Option_Some(((self).p).GetClass(d_691_n_, 0))
                    return iife7_(_pat_let3_0)
                return iife6_(d_690___mcc_h1_)

        d_689_s2_ = lambda28_(((self).a).Succ(x, True))
        return (d_686_s1_, d_689_s2_)

    def SplitFrom(self):
        def lambda29_(d_693_k_):
            def lambda30_(d_694_k_):
                def lambda31_(d_695_y_):
                    return ((self).ClassSucc((SeqOfSets.default__.SetToSequence((((self).p).elem)[d_694_k_]))[0])) == ((self).ClassSucc(d_695_y_))

                return lambda31_

            return lambda30_(d_693_k_)

        d_692_splitterF_ = lambda29_
        d_696_r_ = PartitionMod.default__.SplitAll((self).p, d_692_splitterF_, 0, len(((self).p).elem))
        d_697_dt__update__tmp_h0_ = self
        d_698_dt__update_hp_h0_ = d_696_r_
        return Pair_Pair((d_697_dt__update__tmp_h0_).a, d_698_dt__update_hp_h0_)

    def GenerateReduced(self, index):
        if (index) == (len(((self).p).elem)):
            return _dafny.SeqWithoutIsStrInference([])
        elif True:
            d_699_firstElem_ = (SeqOfSets.default__.SetToSequence((((self).p).elem)[index]))[0]
            d_700_succs_ = (self).ClassSucc(d_699_firstElem_)
            def lambda32_(source59_):
                d_702___mcc_h0_ = source59_[0]
                d_703___mcc_h1_ = source59_[1]
                def lambda33_(source60_):
                    if source60_.is_None:
                        def lambda34_(source61_):
                            if source61_.is_None:
                                return _dafny.SeqWithoutIsStrInference([])
                            elif True:
                                d_704___mcc_h2_ = source61_.v
                                def iife8_(_pat_let4_0):
                                    def iife9_(d_705_sTrue_):
                                        return _dafny.SeqWithoutIsStrInference([(d_699_firstElem_, True, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_705_sTrue_]))[0])])
                                    return iife9_(_pat_let4_0)
                                return iife8_(d_704___mcc_h2_)

                        return lambda34_(d_703___mcc_h1_)
                    elif True:
                        d_706___mcc_h3_ = source60_.v
                        def lambda35_(source62_):
                            if source62_.is_None:
                                def iife10_(_pat_let5_0):
                                    def iife11_(d_707_sFalse_):
                                        return _dafny.SeqWithoutIsStrInference([(d_699_firstElem_, False, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_707_sFalse_]))[0])])
                                    return iife11_(_pat_let5_0)
                                return iife10_(d_706___mcc_h3_)
                            elif True:
                                d_708___mcc_h4_ = source62_.v
                                def iife12_(_pat_let6_0):
                                    def iife13_(d_709_sTrue_):
                                        def iife14_(_pat_let7_0):
                                            def iife15_(d_710_sFalse_):
                                                return _dafny.SeqWithoutIsStrInference([(d_699_firstElem_, False, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_710_sFalse_]))[0]), (d_699_firstElem_, True, (SeqOfSets.default__.SetToSequence((((self).p).elem)[d_709_sTrue_]))[0])])
                                            return iife15_(_pat_let7_0)
                                        return iife14_(d_706___mcc_h3_)
                                    return iife13_(_pat_let6_0)
                                return iife12_(d_708___mcc_h4_)

                        return lambda35_(d_703___mcc_h1_)

                return lambda33_(d_702___mcc_h0_)

            d_701_newEdges_ = lambda32_(((d_700_succs_)[0], (d_700_succs_)[1]))
            return (d_701_newEdges_) + ((self).GenerateReduced((index) + (1)))


class Pair_Pair(Pair, NamedTuple('Pair', [('a', Any), ('p', Any)])):
    def __dafnystr__(self) -> str:
        return f'Minimiser.Pair.Pair({_dafny.string_of(self.a)}, {_dafny.string_of(self.p)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Pair_Pair) and self.a == __o.a and self.p == __o.p
    def __hash__(self) -> int:
        return super().__hash__()

