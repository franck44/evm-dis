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
        def lambda76_(d_1058_noTable_):
            def lambda77_(d_1059_s_):
                return ((self).prog).ToHTML(d_1059_s_, not(d_1058_noTable_), (MiscTypes.Option_None() if (d_1059_s_).is_ErrorGState else MiscTypes.Option_Some(len((d_1059_s_).st))))

            return lambda77_

        def lambda78_(d_1060_s_, d_1061_l_, d_1062___v0_):
            return ((self).prog).DotLabel(d_1060_s_, d_1061_l_)

        ((self).a).ToDot(lambda76_(noTable), lambda78_, (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "graph[labelloc=\"t\", labeljust=\"l\", label=<"))) + ((self).MakeTitle(name, ((self).a).SSize(), ((self).a).TSize(0), (self).maxDepth, ((self).stats).maxDepthReached))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "node [shape=none, fontname=arial, style=\"rounded, filled\", fillcolor= \"whitesmoke\"]\nedge [fontname=arial]\nranking=TB"))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "G")))
        if not((self).minimised):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Raw CFG -------------------\n"))).VerbatimString(False))
        elif True:
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Minimised CFG -------------------\n"))).VerbatimString(False))

    def ReachableInvalidSegs(self):
        def lambda79_(d_1063_s_):
            return (((d_1063_s_).is_EGState) and ((d_1063_s_).IsBounded(len(((self).prog).xs)))) and (((((self).prog).xs)[(d_1063_s_).segNum]).is_INVALIDSeg)

        return MiscTypes.default__.Filter(((self).a).states, lambda79_)

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
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "include \"/Users/franck/development/evm-dis/src/dafny/AbstractSemantics/AbstractSemantics.dfy\""))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "module "))) + (name)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " {")))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened AbstractSemantics"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened AbstractState"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        (self).PrintCFGVerifierBody(0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def PrintProofObjectBody(self, index):
        _this = self
        while True:
            with _dafny.label():
                if (index) < (len(((_this).a).states)):
                    d_1064_currentState_: CFGState.GState
                    d_1064_currentState_ = (((_this).a).states)[index]
                    d_1065_startAddress_: int
                    d_1065_startAddress_ = ((_this).prog).StartAddress((d_1064_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Node "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(index))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Segment Id for this node is: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1064_currentState_).segNum))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Starting at 0x"))).VerbatimString(False))
                    _dafny.print((Hex.default__.NatToHex(d_1065_startAddress_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Segment type is: "))).VerbatimString(False))
                    _dafny.print((((((_this).prog).xs)[(d_1064_currentState_).segNum]).SegTypeName()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Minimum stack size for this segment to prevent stack underflow: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(((_this).prog).WpOp((d_1064_currentState_).segNum)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1066_minCap_: int
                    d_1066_minCap_ = ((_this).prog).WpCap((d_1064_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Minimum capacity for this segment to prevent stack overflow: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_1066_minCap_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1067_netStackEffect_: int
                    d_1067_netStackEffect_ = ((_this).prog).StackEffect((d_1064_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Net Stack Effect: "))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+")) if (d_1067_netStackEffect_) >= (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_1067_netStackEffect_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1068_netCapEffect_: int
                    d_1068_netCapEffect_ = ((_this).prog).CapEffect((d_1064_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Net Capacity Effect: "))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+")) if (d_1068_netCapEffect_) >= (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_1068_netCapEffect_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "*/\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function {:opaque} {:verify false} ExecuteFromCFGNode_s"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(index))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EState, gas: nat): (s': EState)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // PC requirement for this node."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.pc == 0x"))).VerbatimString(False))
                    _dafny.print((Hex.default__.NatToHex(d_1065_startAddress_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as nat\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Stack requirements for this node."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.IsValid() \n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.Operands()"))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " == ")) if (index) == (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " >= ")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((d_1064_currentState_).st)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    hi8_ = len((d_1064_currentState_).st)
                    for d_1069_k_ in range(0, hi8_):
                        if (((d_1064_currentState_).st)[d_1069_k_]).is_Value:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n  requires s0.stack["))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_1069_k_))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "] == "))).VerbatimString(False))
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex((((d_1064_currentState_).st)[d_1069_k_]).Extract()))).VerbatimString(False))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  decreases gas\n"))).VerbatimString(False))
                    d_1070_nodeInstructions_: _dafny.Seq
                    d_1070_nodeInstructions_ = ((((_this).prog).xs)[(d_1064_currentState_).segNum]).ins
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "{\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "if gas == 0 then Revert(s0)"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "else\n"))).VerbatimString(False))
                    (_this).PrintInstructionsToDafny(d_1070_nodeInstructions_, State.AState_EState(d_1065_startAddress_, (d_1064_currentState_).st), 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "   "))).VerbatimString(False))
                    _dafny.print((PrettyIns.default__.PrintInstructionToDafny(((((_this).prog).xs)[(d_1064_currentState_).segNum]).lastIns, len(d_1070_nodeInstructions_), (len(d_1070_nodeInstructions_)) + (1))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if (len(((_this).a).SuccNat(index))) == (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_1070_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif (len(((_this).a).SuccNat(index))) == (1):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // jump to the successor Next() or Tgt of JUMP;\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[0]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_1070_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)\n"))).VerbatimString(False))
                    elif True:
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  if s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(len(d_1070_nodeInstructions_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ".stack[1] > 0 then "))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n   ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[1]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_1070_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  else"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "     ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[0]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_1070_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))
                    in168_ = _this
                    in169_ = (index) + (1)
                    _this = in168_
                    
                    index = in169_
                    raise _dafny.TailCall()
                break

    def PrintCFGVerifierBody(self, index):
        _this = self
        while True:
            with _dafny.label():
                if (index) < (len(((_this).a).states)):
                    d_1071_currentState_: CFGState.GState
                    d_1071_currentState_ = (((_this).a).states)[index]
                    d_1072_startAddress_: int
                    d_1072_startAddress_ = ((_this).prog).StartAddress((d_1071_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Node "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(index))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Segment Id for this node is: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1071_currentState_).segNum))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Starting at 0x"))).VerbatimString(False))
                    _dafny.print((Hex.default__.NatToHex(d_1072_startAddress_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Segment type is: "))).VerbatimString(False))
                    _dafny.print((((((_this).prog).xs)[(d_1071_currentState_).segNum]).SegTypeName()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Minimum stack size for this segment to prevent stack underflow: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(((_this).prog).WpOp((d_1071_currentState_).segNum)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1073_minCap_: int
                    d_1073_minCap_ = ((_this).prog).WpCap((d_1071_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Minimum capacity for this segment to prevent stack overflow: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_1073_minCap_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1074_netStackEffect_: int
                    d_1074_netStackEffect_ = ((_this).prog).StackEffect((d_1071_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Net Stack Effect: "))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+")) if (d_1074_netStackEffect_) >= (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_1074_netStackEffect_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1075_netCapEffect_: int
                    d_1075_netCapEffect_ = ((_this).prog).CapEffect((d_1071_currentState_).segNum)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "* Net Capacity Effect: "))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+")) if (d_1075_netCapEffect_) >= (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_1075_netCapEffect_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "*/\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function {:opaque} {:verify true} ExecuteFromCFGNode_s"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(index))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EState, gas: nat): (s': EState)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // PC requirement for this node."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.pc == 0x"))).VerbatimString(False))
                    _dafny.print((Hex.default__.NatToHex(d_1072_startAddress_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as nat\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Stack requirements for this node."))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.Operands()"))).VerbatimString(False))
                    _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " >= ")) if (index) == (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " >= ")))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((d_1071_currentState_).st)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    hi9_ = len((d_1071_currentState_).st)
                    for d_1076_k_ in range(0, hi9_):
                        if (((d_1071_currentState_).st)[d_1076_k_]).is_Value:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n  requires s0.stack["))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_1076_k_))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "] == "))).VerbatimString(False))
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex((((d_1071_currentState_).st)[d_1076_k_]).Extract()))).VerbatimString(False))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  decreases gas\n"))).VerbatimString(False))
                    d_1077_nodeInstructions_: _dafny.Seq
                    d_1077_nodeInstructions_ = ((((_this).prog).xs)[(d_1071_currentState_).segNum]).ins
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "{\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "if gas == 0 then s0"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "else\n"))).VerbatimString(False))
                    (_this).PrintInstructionsToDafny(d_1077_nodeInstructions_, State.AState_EState(d_1072_startAddress_, (d_1071_currentState_).st), 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((PrettyIns.default__.PrintInstructionToDafny(((((_this).prog).xs)[(d_1071_currentState_).segNum]).lastIns, len(d_1077_nodeInstructions_), (len(d_1077_nodeInstructions_)) + (1))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if (len(((_this).a).SuccNat(index))) == (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Segment is terminal (Revert, Stop or Return)\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_1077_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif (len(((_this).a).SuccNat(index))) == (1):
                        d_1078_commLine_: _dafny.Seq
                        def lambda80_(source72_):
                            if source72_.is_JUMPSeg:
                                d_1079___mcc_h0_ = source72_.ins
                                d_1080___mcc_h1_ = source72_.lastIns
                                d_1081___mcc_h2_ = source72_.netOpEffect
                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//  JUMP to the target at Peek(0)"))
                            elif source72_.is_JUMPISeg:
                                d_1082___mcc_h6_ = source72_.ins
                                d_1083___mcc_h7_ = source72_.lastIns
                                d_1084___mcc_h8_ = source72_.netOpEffect
                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Segment has one successor but is not a JUMP nor a CONT"))
                            elif source72_.is_RETURNSeg:
                                d_1085___mcc_h12_ = source72_.ins
                                d_1086___mcc_h13_ = source72_.lastIns
                                d_1087___mcc_h14_ = source72_.netOpEffect
                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Segment has one successor but is not a JUMP nor a CONT"))
                            elif source72_.is_STOPSeg:
                                d_1088___mcc_h18_ = source72_.ins
                                d_1089___mcc_h19_ = source72_.lastIns
                                d_1090___mcc_h20_ = source72_.netOpEffect
                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Segment has one successor but is not a JUMP nor a CONT"))
                            elif source72_.is_CONTSeg:
                                d_1091___mcc_h24_ = source72_.ins
                                d_1092___mcc_h25_ = source72_.lastIns
                                d_1093___mcc_h26_ = source72_.netOpEffect
                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//  Go to the next instruction at pc + 1"))
                            elif True:
                                d_1094___mcc_h30_ = source72_.ins
                                d_1095___mcc_h31_ = source72_.lastIns
                                d_1096___mcc_h32_ = source72_.netOpEffect
                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Segment has one successor but is not a JUMP nor a CONT"))

                        d_1078_commLine_ = lambda80_((((_this).prog).xs)[(d_1071_currentState_).segNum])
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                        _dafny.print((d_1078_commLine_).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[0]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_1077_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)\n"))).VerbatimString(False))
                    elif True:
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // This is a JUMPI segment, determine next pc using second top-most element of stack\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  if s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(len(d_1077_nodeInstructions_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ".stack[1] > 0 then\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "   ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[1]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_1077_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  else\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "    ExecuteFromCFGNode_s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((((_this).a).SuccNat(index))[0]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((len(d_1077_nodeInstructions_)) + (1)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", gas - 1)"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))
                    in170_ = _this
                    in171_ = (index) + (1)
                    _this = in170_
                    
                    index = in171_
                    raise _dafny.TailCall()
                break

    def PrintInstructionsToDafny(self, xs, currentState, pos):
        _this = self
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_1097_k_: _dafny.Seq
                    d_1097_k_ = PrettyIns.default__.PrintInstructionToDafny((xs)[0], pos, (pos) + (1))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((d_1097_k_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1098_newState_: State.AState
                    d_1098_newState_ = (((xs)[0]).NextState(currentState, ((_this).prog).jumpDests, 0) if (currentState).is_EState else currentState)
                    if ((d_1098_newState_).is_EState) and ((_dafny.euclidian_modulus(pos, 2)) == (0)):
                        hi10_ = len((d_1098_newState_).stack)
                        for d_1099_j_ in range(0, hi10_):
                            if (((d_1098_newState_).stack)[d_1099_j_]).is_Value:
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  assert s"))).VerbatimString(False))
                                _dafny.print(_dafny.string_of((pos) + (1)))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ".stack["))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_1099_j_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "] == "))).VerbatimString(False))
                                _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex((((d_1098_newState_).stack)[d_1099_j_]).Extract()))).VerbatimString(False))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ";\n"))).VerbatimString(False))
                    in172_ = _this
                    in173_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in174_ = d_1098_newState_
                    in175_ = (pos) + (1)
                    _this = in172_
                    
                    xs = in173_
                    currentState = in174_
                    pos = in175_
                    raise _dafny.TailCall()
                break


class CFGObj_CFGObj(CFGObj, NamedTuple('CFGObj', [('prog', Any), ('maxDepth', Any), ('a', Any), ('minimised', Any), ('stats', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGObject.CFGObj.CFGObj({_dafny.string_of(self.prog)}, {_dafny.string_of(self.maxDepth)}, {_dafny.string_of(self.a)}, {_dafny.string_of(self.minimised)}, {_dafny.string_of(self.stats)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CFGObj_CFGObj) and self.prog == __o.prog and self.maxDepth == __o.maxDepth and self.a == __o.a and self.minimised == __o.minimised and self.stats == __o.stats
    def __hash__(self) -> int:
        return super().__hash__()

