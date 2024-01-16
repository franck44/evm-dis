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
import GStateMinimiser

# Module: Statistics

class default__:
    def  __init__(self):
        pass

    @_dafny.classproperty
    def DEFAULT__STATS(instance):
        return Stats_Stats(False, 0, 0, 0, (0, 0))

class Stats:
    @classmethod
    def default(cls, ):
        return lambda: Stats_Stats(False, int(0), int(0), int(0), (int(0), int(0)))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Stats(self) -> bool:
        return isinstance(self, Stats_Stats)
    def SetMaxDepth(self):
        d_888_dt__update__tmp_h0_ = self
        d_889_dt__update_hmaxDepthReached_h0_ = True
        return Stats_Stats(d_889_dt__update_hmaxDepthReached_h0_, (d_888_dt__update__tmp_h0_).visitedStates, (d_888_dt__update__tmp_h0_).wPreInvSuccess, (d_888_dt__update__tmp_h0_).errorState, (d_888_dt__update__tmp_h0_).nonMinimisedSize)

    def IncVisited(self):
        d_890_dt__update__tmp_h0_ = self
        d_891_dt__update_hvisitedStates_h0_ = ((self).visitedStates) + (1)
        return Stats_Stats((d_890_dt__update__tmp_h0_).maxDepthReached, d_891_dt__update_hvisitedStates_h0_, (d_890_dt__update__tmp_h0_).wPreInvSuccess, (d_890_dt__update__tmp_h0_).errorState, (d_890_dt__update__tmp_h0_).nonMinimisedSize)

    def IncWpre(self):
        d_892_dt__update__tmp_h0_ = self
        d_893_dt__update_hwPreInvSuccess_h0_ = ((self).wPreInvSuccess) + (1)
        return Stats_Stats((d_892_dt__update__tmp_h0_).maxDepthReached, (d_892_dt__update__tmp_h0_).visitedStates, d_893_dt__update_hwPreInvSuccess_h0_, (d_892_dt__update__tmp_h0_).errorState, (d_892_dt__update__tmp_h0_).nonMinimisedSize)

    def IncError(self):
        d_894_dt__update__tmp_h0_ = self
        d_895_dt__update_herrorState_h0_ = ((self).errorState) + (1)
        return Stats_Stats((d_894_dt__update__tmp_h0_).maxDepthReached, (d_894_dt__update__tmp_h0_).visitedStates, (d_894_dt__update__tmp_h0_).wPreInvSuccess, d_895_dt__update_herrorState_h0_, (d_894_dt__update__tmp_h0_).nonMinimisedSize)

    def PrettyPrint(self):
        return (((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MaxDepth reached:"))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if (self).maxDepthReached else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorStates reached:")))) + (Int.default__.NatToString((self).errorState))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "States seen:")))) + (Int.default__.NatToString((self).visitedStates))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WPre success:")))) + (Int.default__.NatToString((self).wPreInvSuccess))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))


class Stats_Stats(Stats, NamedTuple('Stats', [('maxDepthReached', Any), ('visitedStates', Any), ('wPreInvSuccess', Any), ('errorState', Any), ('nonMinimisedSize', Any)])):
    def __dafnystr__(self) -> str:
        return f'Statistics.Stats.Stats({_dafny.string_of(self.maxDepthReached)}, {_dafny.string_of(self.visitedStates)}, {_dafny.string_of(self.wPreInvSuccess)}, {_dafny.string_of(self.errorState)}, {_dafny.string_of(self.nonMinimisedSize)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Stats_Stats) and self.maxDepthReached == __o.maxDepthReached and self.visitedStates == __o.visitedStates and self.wPreInvSuccess == __o.wPreInvSuccess and self.errorState == __o.errorState and self.nonMinimisedSize == __o.nonMinimisedSize
    def __hash__(self) -> int:
        return super().__hash__()

