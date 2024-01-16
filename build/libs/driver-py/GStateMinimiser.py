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
import PartitionMod

# Module: GStateMinimiser

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def MakeInit(aut, clazz):
        return Pair_Pair(aut, clazz)

    @_dafny.classproperty
    def DEFAULT__STATE(instance):
        return CFGState.default__.DEFAULT__GSTATE

class ValidPair:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Pair_Pair((Automata.Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({}))).AddState(default__.DEFAULT__STATE), PartitionMod.default__.MakeInit(1))

class Pair:
    @classmethod
    def default(cls, ):
        return lambda: Pair_Pair(Automata.ValidAuto.default(), PartitionMod.ValidPartition.default())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Pair(self) -> bool:
        return isinstance(self, Pair_Pair)
    def ClassSucc(self, x):
        d_879_l_ = ((self).aut).SuccNat(x)
        return _dafny.SeqWithoutIsStrInference([((self).clazz).GetClass((d_879_l_)[d_880_z_], 0) for d_880_z_ in range(len(d_879_l_))])

    def ClassSplitter(self):
        d_881_dt__update__tmp_h0_ = self
        d_882_dt__update_hclazz_h0_ = ((self).clazz).RefineAll(self.Splitter)
        return Pair_Pair((d_881_dt__update__tmp_h0_).aut, d_882_dt__update_hclazz_h0_)

    def Splitter(self, x, y):
        return ((self).ClassSucc(x)) == ((self).ClassSucc(y))

    def Minimise(self):
        d_883_p1_ = Pair.IterSplit(self)
        return (d_883_p1_).MapToClasses(Automata.Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({})), 0)

    def MapToClasses(self, acc, index):
        if (index) == (len(((self).aut).states)):
            return acc
        elif True:
            def lambda42_(d_885_i_):
                return (((self).aut).states)[d_885_i_]

            d_884_succs_ = MiscTypes.default__.MapP(((self).clazz).GetClassRepOfSeqs((((self).aut).transitionsNat)[index]), lambda42_)
            d_886_a_k_ = (self).MapToClasses((acc).AddEdges((((self).aut).states)[((self).clazz).GetClassRepOf(index)], d_884_succs_, 0), (index) + (1))
            return d_886_a_k_

    @staticmethod
    def IterSplit(pp):
        while True:
            with _dafny.label():
                d_887_p1_ = (pp).ClassSplitter()
                if (len(((d_887_p1_).clazz).elem)) == (len(((pp).clazz).elem)):
                    return pp
                elif True:
                    in127_ = d_887_p1_
                    pp = in127_
                    raise _dafny.TailCall()
                break


class Pair_Pair(Pair, NamedTuple('Pair', [('aut', Any), ('clazz', Any)])):
    def __dafnystr__(self) -> str:
        return f'GStateMinimiser.Pair.Pair({_dafny.string_of(self.aut)}, {_dafny.string_of(self.clazz)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Pair_Pair) and self.aut == __o.aut and self.clazz == __o.clazz
    def __hash__(self) -> int:
        return super().__hash__()

