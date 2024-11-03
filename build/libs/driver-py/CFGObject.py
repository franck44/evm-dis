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
import Statistics as Statistics
import HTML as HTML
import EVMObject as EVMObject
import ArgParser as ArgParser

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
    def HasNoErrorState(self):
        return ((self).prog).HasNoErrorState((self).a)

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
        def lambda0_(d_0_noTable_):
            def lambda1_(d_1_s_, d_2_k_):
                return ((self).prog).ToHTML(d_1_s_, not(d_0_noTable_), (MiscTypes.Option_None() if (d_1_s_).is_ErrorGState else MiscTypes.Option_Some(len((d_1_s_).st))), d_2_k_)

            return lambda1_

        def lambda2_(d_3_s_, d_4_l_, d_5___v0_):
            return ((self).prog).DotLabel(d_3_s_, d_4_l_)

        ((self).a).ToDot(lambda0_(noTable), lambda2_, (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "graph[labelloc=\"t\", labeljust=\"l\", label=<"))) + ((self).MakeTitle(name, ((self).a).SSize(), ((self).a).TSize(0), (self).maxDepth, ((self).stats).maxDepthReached))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "node [shape=none, fontname=arial, style=\"rounded, filled\", fillcolor= \"whitesmoke\"]\nedge [fontname=arial]\nranking=TB"))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "G")))
        if not((self).minimised):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Raw CFG -------------------\n"))).VerbatimString(False))
        elif True:
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Minimised CFG -------------------\n"))).VerbatimString(False))

    def ReachableInvalidSegs(self):
        def lambda0_(d_0_s_):
            return (((d_0_s_).is_EGState) and ((d_0_s_).IsBounded(len(((self).prog).xs)))) and (((((self).prog).xs)[(d_0_s_).segNum]).is_INVALIDSeg)

        return MiscTypes.default__.Filter(((self).a).states, lambda0_)

    def MakeTitle(self, name, numNodes, numEdges, maxDepth, reached):
        return (((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Program Name: </B> "))) + (name)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"left\"/>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Control Flow Graph Info: </B><BR ALIGN=\"left\"/>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth: ")))) + (Int.default__.NatToString(maxDepth))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Was reached")) if reached else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Was not reached"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"left\"/>")))) + (Int.default__.NatToString(numNodes))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes/")))) + (Int.default__.NatToString(numEdges))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges<BR ALIGN=\"left\"/>")))

    def ToDafny(self, name, pathToEVMDafny):
        if (len(pathToEVMDafny)) > (0):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "include \"./src/dafny/AbstractSemantics/AbstractSemantics.dfy\""))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "module "))) + (name)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " {")))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened AbstractSemantics"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened AbstractState"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        (self).PrintProofObjectBody(0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def CFGCheckerToDafny(self, name, pathToEVMDafny):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "include \"../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy\""))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "module  {:disableNonlinearArithmetic} "))) + (name)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " {")))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened AbstractSemantics"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened AbstractState"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        (self).PrintCFGVerifierBody(0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def CFGRefineToDafny(self, name, pathToEVMDafny):
        _dafny.print(((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "include "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (pathToEVMDafny)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/src/dafny/state.dfy\"")))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print(((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "include "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (pathToEVMDafny)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/src/dafny/bytecode.dfy\"")))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "module {:disableNonlinearArithmetic} "))) + (name)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " {")))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import EvmState"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened Bytecode"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function SafeJump(s: EvmState.State): (s': EvmState.State)"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        (self).PrintProofObjectBody(0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def PrintProofObjectBody(self, index):
        _this = self
        while True:
            with _dafny.label():
                if (index) < (len(((_this).a).states)):
                    d_0_currentState_: CFGState.GState
                    d_0_currentState_ = (((_this).a).states)[index]
                    d_1_startAddress_: int
                    d_1_startAddress_ = ((_this).prog).StartAddress((d_0_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Node "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(index))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Segment Id for this node is: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_0_currentState_).segNum))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Starting at 0x"))).VerbatimString(False))
                    _dafny.print((Hex.default__.NatToHex(d_1_startAddress_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Segment type is: "))).VerbatimString(False))
                    _dafny.print((((((_this).prog).xs)[(d_0_currentState_).segNum]).SegTypeName()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Minimum stack size for this segment to prevent stack underflow: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(((_this).prog).WpOp((d_0_currentState_).segNum)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_2_minCap_: int
                    d_2_minCap_ = ((_this).prog).WpCap((d_0_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Minimum capacity for this segment to prevent stack overflow: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_2_minCap_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_3_netStackEffect_: int
                    d_3_netStackEffect_ = ((_this).prog).StackEffect((d_0_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Net Stack Effect: "))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+")) if (d_3_netStackEffect_) >= (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_3_netStackEffect_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_4_netCapEffect_: int
                    d_4_netCapEffect_ = ((_this).prog).CapEffect((d_0_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Net Capacity Effect: "))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+")) if (d_4_netCapEffect_) >= (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_4_netCapEffect_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "*/\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function ExecuteFromCFGNode_s"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(index))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EvmState.State): (s': EvmState.State)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Writes permission for this segment."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // PC requirement for this node."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.EXECUTING?"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.WritesPermitted()"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.PC() == 0x"))).VerbatimString(False))
                    _dafny.print((Hex.default__.NatToHex(d_1_startAddress_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as nat\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Stack requirements for this node."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.Operands()"))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " == ")) if (index) == (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " >= ")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((d_0_currentState_).st)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.Capacity() >= "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_2_minCap_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    hi0_ = len((d_0_currentState_).st)
                    for d_5_k_ in range(0, hi0_):
                        if (((d_0_currentState_).st)[d_5_k_]).is_Value:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n  requires s0.Peek("))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_5_k_))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ") == "))).VerbatimString(False))
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex((((d_0_currentState_).st)[d_5_k_]).Extract()))).VerbatimString(False))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    def lambda0_():
                        source0_ = (((_this).prog).xs)[(d_0_currentState_).segNum]
                        if True:
                            if source0_.is_STOPSeg:
                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures  s'.ERROR?\n"))
                        if True:
                            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures  s'.EXECUTING??\n"))

                    _dafny.print((lambda0_()).VerbatimString(False))
                    d_6_nodeInstructions_: _dafny.Seq
                    d_6_nodeInstructions_ = ((((_this).prog).xs)[(d_0_currentState_).segNum]).ins
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "{\n"))).VerbatimString(False))
                    (_this).PrintInstructionsToDafny(d_6_nodeInstructions_, State.AState_EState(d_1_startAddress_, (d_0_currentState_).st), 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "   "))).VerbatimString(False))
                    _dafny.print((PrettyIns.default__.PrintInstructionToDafny(((((_this).prog).xs)[(d_0_currentState_).segNum]).lastIns, len(d_6_nodeInstructions_), (len(d_6_nodeInstructions_)) + (1))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  s"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((len(d_6_nodeInstructions_)) + (1)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))
                    in0_ = _this
                    in1_ = (index) + (1)
                    _this = in0_
                    
                    index = in1_
                    raise _dafny.TailCall()
                break

    def PrintCFGVerifierBody(self, index):
        _this = self
        while True:
            with _dafny.label():
                if (index) < (len(((_this).a).states)):
                    d_0_currentState_: CFGState.GState
                    d_0_currentState_ = (((_this).a).states)[index]
                    d_1_startAddress_: int
                    d_1_startAddress_ = ((_this).prog).StartAddress((d_0_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Node "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(index))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Segment Id for this node is: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_0_currentState_).segNum))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Starting at 0x"))).VerbatimString(False))
                    _dafny.print((Hex.default__.NatToHex(d_1_startAddress_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Segment type is: "))).VerbatimString(False))
                    _dafny.print((((((_this).prog).xs)[(d_0_currentState_).segNum]).SegTypeName()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Minimum stack size for this segment to prevent stack underflow: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(((_this).prog).WpOp((d_0_currentState_).segNum)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_2_minCap_: int
                    d_2_minCap_ = ((_this).prog).WpCap((d_0_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Minimum capacity for this segment to prevent stack overflow: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_2_minCap_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_3_netStackEffect_: int
                    d_3_netStackEffect_ = ((_this).prog).StackEffect((d_0_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Net Stack Effect: "))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+")) if (d_3_netStackEffect_) >= (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_3_netStackEffect_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_4_netCapEffect_: int
                    d_4_netCapEffect_ = ((_this).prog).CapEffect((d_0_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Net Capacity Effect: "))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+")) if (d_4_netCapEffect_) >= (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_4_netCapEffect_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "*/\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function {:opaque} {:verify true} ExecuteFromCFGNode_s"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(index))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EState, gas: nat): (s': EState)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // PC requirement for this node."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.pc == 0x"))).VerbatimString(False))
                    _dafny.print((Hex.default__.NatToHex(d_1_startAddress_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as nat\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Stack requirements for this node."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.Operands()"))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " >= ")) if (index) == (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " >= ")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((d_0_currentState_).st)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    hi0_ = len((d_0_currentState_).st)
                    for d_5_k_ in range(0, hi0_):
                        if (((d_0_currentState_).st)[d_5_k_]).is_Value:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n  requires s0.stack["))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_5_k_))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "] == "))).VerbatimString(False))
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex((((d_0_currentState_).st)[d_5_k_]).Extract()))).VerbatimString(False))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  decreases gas\n"))).VerbatimString(False))
                    d_6_nodeInstructions_: _dafny.Seq
                    d_6_nodeInstructions_ = ((((_this).prog).xs)[(d_0_currentState_).segNum]).ins
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "{\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "if gas == 0 then s0"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "else\n"))).VerbatimString(False))
                    (_this).PrintInstructionsToDafny(d_6_nodeInstructions_, State.AState_EState(d_1_startAddress_, (d_0_currentState_).st), 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((PrettyIns.default__.PrintInstructionToDafny(((((_this).prog).xs)[(d_0_currentState_).segNum]).lastIns, len(d_6_nodeInstructions_), (len(d_6_nodeInstructions_)) + (1))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if (len(((_this).a).SuccNat(index))) == (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Segment is terminal (Revert, Stop or Return)\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_6_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif (len(((_this).a).SuccNat(index))) == (1):
                        d_7_commLine_: _dafny.Seq
                        source0_ = (((_this).prog).xs)[(d_0_currentState_).segNum]
                        with _dafny.label("match0"):
                            if True:
                                if source0_.is_CONTSeg:
                                    d_7_commLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//  Go to the next instruction at pc + 1"))
                                    raise _dafny.Break("match0")
                            if True:
                                if source0_.is_JUMPSeg:
                                    d_7_commLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//  JUMP to the target at Peek(0)"))
                                    raise _dafny.Break("match0")
                            if True:
                                d_7_commLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Segment has one successor but is not a JUMP nor a CONT"))
                            pass
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                        _dafny.print((d_7_commLine_).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[0]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_6_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)\n"))).VerbatimString(False))
                    elif True:
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // This is a JUMPI segment, determine next pc using second top-most element of stack\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  if s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(len(d_6_nodeInstructions_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ".stack[1] > 0 then\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "   ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[1]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_6_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  else\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "    ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[0]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_6_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))
                    in0_ = _this
                    in1_ = (index) + (1)
                    _this = in0_
                    
                    index = in1_
                    raise _dafny.TailCall()
                break

    def PrintInstructionsToDafny(self, xs, currentState, pos):
        _this = self
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_0_k_: _dafny.Seq
                    d_0_k_ = PrettyIns.default__.PrintInstructionToDafny((xs)[0], pos, (pos) + (1))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((d_0_k_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1_newState_: State.AState
                    if (currentState).is_EState:
                        d_1_newState_ = ((xs)[0]).NextState(currentState, ((_this).prog).jumpDests, 0)
                    elif True:
                        d_1_newState_ = currentState
                    if (((d_1_newState_).is_EState) and ((pos) > (0))) and ((_dafny.euclidian_modulus(pos, 10)) == (0)):
                        hi0_ = len((d_1_newState_).stack)
                        for d_2_j_ in range(0, hi0_):
                            if (((d_1_newState_).stack)[d_2_j_]).is_Value:
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "   assert s"))).VerbatimString(False))
                                _dafny.print(_dafny.string_of((pos) + (1)))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ".Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_2_j_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ") == "))).VerbatimString(False))
                                _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex((((d_1_newState_).stack)[d_2_j_]).Extract()))).VerbatimString(False))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ";\n"))).VerbatimString(False))
                    in0_ = _this
                    in1_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in2_ = d_1_newState_
                    in3_ = (pos) + (1)
                    _this = in0_
                    
                    xs = in1_
                    currentState = in2_
                    pos = in3_
                    raise _dafny.TailCall()
                break


class CFGObj_CFGObj(CFGObj, NamedTuple('CFGObj', [('prog', Any), ('maxDepth', Any), ('a', Any), ('minimised', Any), ('stats', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGObject.CFGObj.CFGObj({_dafny.string_of(self.prog)}, {_dafny.string_of(self.maxDepth)}, {_dafny.string_of(self.a)}, {_dafny.string_of(self.minimised)}, {_dafny.string_of(self.stats)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CFGObj_CFGObj) and self.prog == __o.prog and self.maxDepth == __o.maxDepth and self.a == __o.a and self.minimised == __o.minimised and self.stats == __o.stats
    def __hash__(self) -> int:
        return super().__hash__()

