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
import PartitionMod as PartitionMod

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
        d_0_l_ = ((self).aut).SuccNat(x)
        return _dafny.SeqWithoutIsStrInference([((self).clazz).GetClass((d_0_l_)[d_1_z_], 0) for d_1_z_ in range(len(d_0_l_))])

    def ClassSplitter(self):
        d_0_dt__update__tmp_h0_ = self
        d_1_dt__update_hclazz_h0_ = ((self).clazz).RefineAll(self.Splitter)
        return Pair_Pair((d_0_dt__update__tmp_h0_).aut, d_1_dt__update_hclazz_h0_)

    def Splitter(self, x, y):
        return ((self).ClassSucc(x)) == ((self).ClassSucc(y))

    def Minimise(self):
        d_0_p1_ = Pair.IterSplit(self)
        return (d_0_p1_).MapToClasses(Automata.Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({})), 0)

    def MapToClasses(self, acc, index):
        if (index) == (len(((self).aut).states)):
            return acc
        elif True:
            def lambda0_(d_1_i_):
                return (((self).aut).states)[d_1_i_]

            d_0_succs_ = MiscTypes.default__.MapP(((self).clazz).GetClassRepOfSeqs((((self).aut).transitionsNat)[index]), lambda0_)
            d_2_a_k_ = (self).MapToClasses((acc).AddEdges((((self).aut).states)[((self).clazz).GetClassRepOf(index)], d_0_succs_, 0), (index) + (1))
            return d_2_a_k_

    @staticmethod
    def IterSplit(pp):
        while True:
            with _dafny.label():
                d_0_p1_ = (pp).ClassSplitter()
                if (len(((d_0_p1_).clazz).elem)) == (len(((pp).clazz).elem)):
                    return pp
                elif True:
                    in0_ = d_0_p1_
                    pp = in0_
                    raise _dafny.TailCall()
                break


class Pair_Pair(Pair, NamedTuple('Pair', [('aut', Any), ('clazz', Any)])):
    def __dafnystr__(self) -> str:
        return f'GStateMinimiser.Pair.Pair({_dafny.string_of(self.aut)}, {_dafny.string_of(self.clazz)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Pair_Pair) and self.aut == __o.aut and self.clazz == __o.clazz
    def __hash__(self) -> int:
        return super().__hash__()

