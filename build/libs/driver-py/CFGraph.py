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
import State
import WeakPre
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

# Module: CFGraph

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BoolsToString(x):
        d_592___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_592___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "E")))
                elif True:
                    d_592___accumulator_ = (d_592___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_dafny.CodePoint('1') if (x)[0] else _dafny.CodePoint('0'))]))
                    in66_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in66_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DOTSeg(xs, numSeg):
        d_593_s_ = (xs)[numSeg]
        d_594_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex((d_593_s_).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"CENTER\"/>\n")))
        d_595_body_ = default__.DOTIns((d_593_s_).Ins())
        return (d_594_prefix_) + (d_595_body_)

    @staticmethod
    def DOTIns(xi):
        d_596___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_596___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_597_a_ = (((xi)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))
                    d_596___accumulator_ = (d_596___accumulator_) + (d_597_a_)
                    in67_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in67_
                    raise _dafny.TailCall()
                break


class CFGNode:
    @classmethod
    def default(cls, ):
        return lambda: CFGNode_CFGNode(_dafny.Seq({}), MiscTypes.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CFGNode(self) -> bool:
        return isinstance(self, CFGNode_CFGNode)
    def ToString(self):
        return default__.BoolsToString((self).id)


class CFGNode_CFGNode(CFGNode, NamedTuple('CFGNode', [('id', Any), ('seg', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.CFGNode.CFGNode({_dafny.string_of(self.id)}, {_dafny.string_of(self.seg)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CFGNode_CFGNode) and self.id == __o.id and self.seg == __o.seg
    def __hash__(self) -> int:
        return super().__hash__()


class BoolEdge:
    @classmethod
    def default(cls, ):
        return lambda: BoolEdge_BoolEdge(CFGNode.default()(), False, CFGNode.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_BoolEdge(self) -> bool:
        return isinstance(self, BoolEdge_BoolEdge)
    def DOTPrint(self):
        d_598_lab_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if (self).lab else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false")))
        return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [label=")))) + (d_598_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))


class BoolEdge_BoolEdge(BoolEdge, NamedTuple('BoolEdge', [('src', Any), ('lab', Any), ('tgt', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolEdge.BoolEdge({_dafny.string_of(self.src)}, {_dafny.string_of(self.lab)}, {_dafny.string_of(self.tgt)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolEdge_BoolEdge) and self.src == __o.src and self.lab == __o.lab and self.tgt == __o.tgt
    def __hash__(self) -> int:
        return super().__hash__()


class BoolCFGraph:
    @classmethod
    def default(cls, ):
        return lambda: _dafny.Seq({})
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_BoolCFGraph(self) -> bool:
        return isinstance(self, BoolCFGraph_BoolCFGraph)
    @staticmethod
    def AddEdge(self, e):
        return ((self)) + (_dafny.SeqWithoutIsStrInference([e]))

    @staticmethod
    def DOTPrintEdges(self, xe):
        d_599___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xe)) > (0):
                    d_599___accumulator_ = (d_599___accumulator_) + (((xe)[0]).DOTPrint())
                    in68_ = _this
                    in69_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    _this = in68_
                    
                    xe = in69_
                    raise _dafny.TailCall()
                elif True:
                    return (d_599___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    @staticmethod
    def DOTPrintNodes(self, xs, g, printed):
        d_600___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                pat_let_tv1_ = xs
                pat_let_tv2_ = g
                pat_let_tv3_ = xs
                pat_let_tv4_ = g
                if (len(g)) > (0):
                    def iife2_(_pat_let1_0):
                        def iife3_(d_602_numSeg_):
                            def iife4_(_pat_let2_0):
                                def iife5_(d_603_lab_):
                                    return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((pat_let_tv2_)[0]).src).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [label=<\n")))) + (d_603_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))
                                return iife5_(_pat_let2_0)
                            return iife4_((default__.DOTSeg(pat_let_tv1_, (d_602_numSeg_).v) if (d_602_numSeg_).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorEnd <BR ALIGN=\"CENTER\"/>\n"))))
                        return iife3_(_pat_let1_0)
                    d_601_srctxt_ = (iife2_((((g)[0]).src).seg) if (((g)[0]).src) not in (printed) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    def iife6_(_pat_let3_0):
                        def iife7_(d_605_numSeg_):
                            def iife8_(_pat_let4_0):
                                def iife9_(d_606_lab_):
                                    return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((pat_let_tv4_)[0]).tgt).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [label=<\n")))) + (d_606_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))
                                return iife9_(_pat_let4_0)
                            return iife8_((default__.DOTSeg(pat_let_tv3_, (d_605_numSeg_).v) if (d_605_numSeg_).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorEnd <BR ALIGN=\"CENTER\"/>\n"))))
                        return iife7_(_pat_let3_0)
                    d_604_tgttxt_ = (iife6_((((g)[0]).tgt).seg) if ((((g)[0]).tgt) not in (printed)) and ((((g)[0]).src) != (((g)[0]).tgt)) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_600___accumulator_ = (d_600___accumulator_) + ((d_601_srctxt_) + (d_604_tgttxt_))
                    in70_ = _this
                    in71_ = xs
                    in72_ = _dafny.SeqWithoutIsStrInference((g)[1::])
                    in73_ = (printed) | (_dafny.Set({((g)[0]).src, ((g)[0]).tgt}))
                    _this = in70_
                    
                    xs = in71_
                    g = in72_
                    printed = in73_
                    raise _dafny.TailCall()
                elif True:
                    return (d_600___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    @staticmethod
    def DOTPrint(self, xs):
        d_607_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph CFG {\n node [shape=box]\n "))
        return (((d_607_prefix_) + (BoolCFGraph.DOTPrintNodes(self, xs, (self), _dafny.Set({})))) + (BoolCFGraph.DOTPrintEdges(self, (self)))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n")))


class BoolCFGraph_BoolCFGraph(BoolCFGraph, NamedTuple('BoolCFGraph', [('edges', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolCFGraph.BoolCFGraph({_dafny.string_of(self.edges)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolCFGraph_BoolCFGraph) and self.edges == __o.edges
    def __hash__(self) -> int:
        return super().__hash__()

