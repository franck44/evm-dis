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
        d_853_l_ = ((self).aut).SuccNat(x)
        return _dafny.SeqWithoutIsStrInference([((self).clazz).GetClass((d_853_l_)[d_854_z_], 0) for d_854_z_ in range(len(d_853_l_))])

    def ClassSplitter(self):
        d_855_dt__update__tmp_h0_ = self
        d_856_dt__update_hclazz_h0_ = ((self).clazz).RefineAll(self.Splitter)
        return Pair_Pair((d_855_dt__update__tmp_h0_).aut, d_856_dt__update_hclazz_h0_)

    def Splitter(self, x, y):
        return ((self).ClassSucc(x)) == ((self).ClassSucc(y))

    def Minimise(self):
        d_857_p1_ = Pair.IterSplit(self)
        return (d_857_p1_).MapToClasses(Automata.Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({})), 0)

    def MapToClasses(self, acc, index):
        if (index) == (len(((self).aut).states)):
            return acc
        elif True:
            def lambda42_(d_859_i_):
                return (((self).aut).states)[d_859_i_]

            d_858_succs_ = MiscTypes.default__.MapP(((self).clazz).GetClassRepOfSeqs((((self).aut).transitionsNat)[index]), lambda42_)
            d_860_a_k_ = (self).MapToClasses((acc).AddEdges((((self).aut).states)[((self).clazz).GetClassRepOf(index)], d_858_succs_, 0), (index) + (1))
            return d_860_a_k_

    @staticmethod
    def IterSplit(pp):
        while True:
            with _dafny.label():
                d_861_p1_ = (pp).ClassSplitter()
                if (len(((d_861_p1_).clazz).elem)) == (len(((pp).clazz).elem)):
                    return pp
                elif True:
                    in112_ = d_861_p1_
                    pp = in112_
                    raise _dafny.TailCall()
                break


class Pair_Pair(Pair, NamedTuple('Pair', [('aut', Any), ('clazz', Any)])):
    def __dafnystr__(self) -> str:
        return f'GStateMinimiser.Pair.Pair({_dafny.string_of(self.aut)}, {_dafny.string_of(self.clazz)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Pair_Pair) and self.aut == __o.aut and self.clazz == __o.clazz
    def __hash__(self) -> int:
        return super().__hash__()

