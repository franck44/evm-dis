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
import GStateMinimiser
import Statistics
import HTML
import EVMObject
import ArgParser
import ProofObjectBuilder

# Module: CFGObject


class CFGObj:
    @classmethod
    def default(cls, ):
        return lambda: CFGObj_CFGObj(EVMObject.ValidEVMObj.default(), int(0), Automata.ValidAuto.default(), False, Statistics.Stats.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CFGObj(self) -> bool:
        return isinstance(self, CFGObj_CFGObj)
    def ToDot(self, noTable, name):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/*\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
        _dafny.print(_dafny.string_of((self).maxDepth))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((((self).stats).PrettyPrint()).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of reachable invalid segments is: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len((self).ReachableInvalidSegs())))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        if not((self).minimised):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of CFG: "))).VerbatimString(False))
            _dafny.print(_dafny.string_of(((self).a).SSize()))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
            _dafny.print(_dafny.string_of(((self).a).TSize(0)))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "*/\n"))).VerbatimString(False))
        elif True:
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of non minimised CFG: "))).VerbatimString(False))
            _dafny.print(_dafny.string_of((((self).stats).nonMinimisedSize)[0]))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
            _dafny.print(_dafny.string_of((((self).stats).nonMinimisedSize)[1]))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of minimised CFG: "))).VerbatimString(False))
            _dafny.print(_dafny.string_of(((self).a).SSize()))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
            _dafny.print(_dafny.string_of(((self).a).TSize(0)))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "*/\n"))).VerbatimString(False))
        d_1035_wPreOperandsCFG_: MiscTypes.Option
        d_1035_wPreOperandsCFG_ = (self).computeWpre()
        if (d_1035_wPreOperandsCFG_).is_Some:
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Wpre fixpoint status: "))).VerbatimString(False))
            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Reached")) if ((d_1035_wPreOperandsCFG_).v).is_Left else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not reached")))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        def lambda76_(d_1036_noTable_, d_1037_wPreOperandsCFG_):
            def lambda77_(d_1038_s_):
                return (self).PrintState(d_1038_s_, d_1036_noTable_, d_1037_wPreOperandsCFG_)

            return lambda77_

        def lambda78_(d_1039_s_, d_1040_l_, d_1041___v0_):
            return ((self).prog).DotLabel(d_1039_s_, d_1040_l_)

        ((self).a).ToDot(lambda76_(noTable, d_1035_wPreOperandsCFG_), lambda78_, (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "graph[labelloc=\"t\", labeljust=\"l\", label=<"))) + ((self).MakeTitle(name, ((self).a).SSize(), ((self).a).TSize(0), (self).maxDepth, ((self).stats).maxDepthReached))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "node [shape=none, fontname=arial, style=\"rounded, filled\", fillcolor= \"whitesmoke\"]\nedge [fontname=arial]\nranking=TB"))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "G")))
        if not((self).minimised):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Raw CFG -------------------\n"))).VerbatimString(False))
        elif True:
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Minimised CFG -------------------\n"))).VerbatimString(False))

    def computeWpre(self):
        if ((self).prog).HasNoErrorState((self).a):
            return MiscTypes.Option_Some(((self).prog).ComputeWPreOperands((self).a))
        elif True:
            return MiscTypes.Option_None()

    def ExtractWpre(self, r):
        source70_ = r
        if source70_.is_Left:
            d_1042___mcc_h0_ = source70_.l
            d_1043_vv_ = d_1042___mcc_h0_
            return d_1043_vv_
        elif True:
            d_1044___mcc_h1_ = source70_.r
            d_1045_vv_ = d_1044___mcc_h1_
            return d_1045_vv_

    def PrintState(self, s, noTable, wPre):
        if (wPre).is_Some:
            d_1046_wPreValues_ = (self).ExtractWpre((wPre).v)
            return ((self).prog).ToHTML(s, not(noTable), MiscTypes.Option_Some((d_1046_wPreValues_)[(((self).a).indexOf)[s]]))
        elif True:
            return ((self).prog).ToHTML(s, not(noTable), MiscTypes.Option_None())

    def ReachableInvalidSegs(self):
        def lambda79_(d_1047_s_):
            return (((d_1047_s_).is_EGState) and ((d_1047_s_).IsBounded(len(((self).prog).xs)))) and (((((self).prog).xs)[(d_1047_s_).segNum]).is_INVALIDSeg)

        return MiscTypes.default__.Filter(((self).a).states, lambda79_)

    def MakeTitle(self, name, numNodes, numEdges, maxDepth, reached):
        return (((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Program Name: </B> "))) + (name)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"left\"/>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Control Flow Graph Info: </B><BR ALIGN=\"left\"/>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth: ")))) + (Int.default__.NatToString(maxDepth))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Was reached")) if reached else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Was not reached"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"left\"/>")))) + (Int.default__.NatToString(numNodes))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes/")))) + (Int.default__.NatToString(numEdges))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges<BR ALIGN=\"left\"/>")))


class CFGObj_CFGObj(CFGObj, NamedTuple('CFGObj', [('prog', Any), ('maxDepth', Any), ('a', Any), ('minimised', Any), ('stats', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGObject.CFGObj.CFGObj({_dafny.string_of(self.prog)}, {_dafny.string_of(self.maxDepth)}, {_dafny.string_of(self.a)}, {_dafny.string_of(self.minimised)}, {_dafny.string_of(self.stats)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CFGObj_CFGObj) and self.prog == __o.prog and self.maxDepth == __o.maxDepth and self.a == __o.a and self.minimised == __o.minimised and self.stats == __o.stats
    def __hash__(self) -> int:
        return super().__hash__()

