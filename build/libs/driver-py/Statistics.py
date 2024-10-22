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
import GStateMinimiser as GStateMinimiser

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
        d_0_dt__update__tmp_h0_ = self
        d_1_dt__update_hmaxDepthReached_h0_ = True
        return Stats_Stats(d_1_dt__update_hmaxDepthReached_h0_, (d_0_dt__update__tmp_h0_).visitedStates, (d_0_dt__update__tmp_h0_).wPreInvSuccess, (d_0_dt__update__tmp_h0_).errorState, (d_0_dt__update__tmp_h0_).nonMinimisedSize)

    def IncVisited(self):
        d_0_dt__update__tmp_h0_ = self
        d_1_dt__update_hvisitedStates_h0_ = ((self).visitedStates) + (1)
        return Stats_Stats((d_0_dt__update__tmp_h0_).maxDepthReached, d_1_dt__update_hvisitedStates_h0_, (d_0_dt__update__tmp_h0_).wPreInvSuccess, (d_0_dt__update__tmp_h0_).errorState, (d_0_dt__update__tmp_h0_).nonMinimisedSize)

    def IncWpre(self):
        d_0_dt__update__tmp_h0_ = self
        d_1_dt__update_hwPreInvSuccess_h0_ = ((self).wPreInvSuccess) + (1)
        return Stats_Stats((d_0_dt__update__tmp_h0_).maxDepthReached, (d_0_dt__update__tmp_h0_).visitedStates, d_1_dt__update_hwPreInvSuccess_h0_, (d_0_dt__update__tmp_h0_).errorState, (d_0_dt__update__tmp_h0_).nonMinimisedSize)

    def IncError(self):
        d_0_dt__update__tmp_h0_ = self
        d_1_dt__update_herrorState_h0_ = ((self).errorState) + (1)
        return Stats_Stats((d_0_dt__update__tmp_h0_).maxDepthReached, (d_0_dt__update__tmp_h0_).visitedStates, (d_0_dt__update__tmp_h0_).wPreInvSuccess, d_1_dt__update_herrorState_h0_, (d_0_dt__update__tmp_h0_).nonMinimisedSize)

    def PrettyPrint(self):
        return (((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MaxDepth reached:"))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if (self).maxDepthReached else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorStates reached:")))) + (Int.default__.NatToString((self).errorState))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "States seen:")))) + (Int.default__.NatToString((self).visitedStates))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WPre success:")))) + (Int.default__.NatToString((self).wPreInvSuccess))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))


class Stats_Stats(Stats, NamedTuple('Stats', [('maxDepthReached', Any), ('visitedStates', Any), ('wPreInvSuccess', Any), ('errorState', Any), ('nonMinimisedSize', Any)])):
    def __dafnystr__(self) -> str:
        return f'Statistics.Stats.Stats({_dafny.string_of(self.maxDepthReached)}, {_dafny.string_of(self.visitedStates)}, {_dafny.string_of(self.wPreInvSuccess)}, {_dafny.string_of(self.errorState)}, {_dafny.string_of(self.nonMinimisedSize)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Stats_Stats) and self.maxDepthReached == __o.maxDepthReached and self.visitedStates == __o.visitedStates and self.wPreInvSuccess == __o.wPreInvSuccess and self.errorState == __o.errorState and self.nonMinimisedSize == __o.nonMinimisedSize
    def __hash__(self) -> int:
        return super().__hash__()

