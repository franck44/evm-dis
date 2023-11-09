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
import CFGraph

# Module: BuildCFGraph

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildCFGV4(xs, maxDepth, numSeg, s, seen, path):
        pat_let_tv5_ = xs
        pat_let_tv6_ = xs
        pat_let_tv7_ = maxDepth
        pat_let_tv8_ = seen
        pat_let_tv9_ = path
        pat_let_tv10_ = path
        pat_let_tv11_ = numSeg
        pat_let_tv12_ = path
        pat_let_tv13_ = path
        pat_let_tv14_ = numSeg
        pat_let_tv15_ = path
        pat_let_tv16_ = path
        pat_let_tv17_ = numSeg
        pat_let_tv18_ = path
        pat_let_tv19_ = xs
        pat_let_tv20_ = xs
        pat_let_tv21_ = maxDepth
        pat_let_tv22_ = seen
        pat_let_tv23_ = path
        pat_let_tv24_ = path
        pat_let_tv25_ = numSeg
        pat_let_tv26_ = path
        pat_let_tv27_ = path
        pat_let_tv28_ = numSeg
        pat_let_tv29_ = path
        pat_let_tv30_ = path
        pat_let_tv31_ = numSeg
        pat_let_tv32_ = path
        if (maxDepth) == (0):
            return _dafny.SeqWithoutIsStrInference([])
        elif (not(((xs)[numSeg]).HasExit(False))) and (not(((xs)[numSeg]).HasExit(True))):
            return _dafny.SeqWithoutIsStrInference([])
        elif True:
            def iife10_(_pat_let5_0):
                def iife11_(d_609_leftSucc_):
                    def iife12_(_pat_let6_0):
                        def iife13_(d_610_nextSeg_):
                            def iife14_(_pat_let7_0):
                                def iife15_(d_611_gleft_):
                                    return CFGraph.BoolCFGraph.AddEdge(d_611_gleft_, CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv10_, MiscTypes.Option_Some(pat_let_tv11_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv12_) + (_dafny.SeqWithoutIsStrInference([False])), d_610_nextSeg_)))
                                return iife15_(_pat_let7_0)
                            return (iife14_(default__.BuildCFGV4(pat_let_tv6_, (pat_let_tv7_) - (1), (d_610_nextSeg_).v, d_609_leftSucc_, pat_let_tv8_, (pat_let_tv9_) + (_dafny.SeqWithoutIsStrInference([False])))) if (d_610_nextSeg_).is_Some else _dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv13_, MiscTypes.Option_Some(pat_let_tv14_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv15_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]))
                        return iife13_(_pat_let6_0)
                    return (iife12_(default__.PCToSeg(pat_let_tv5_, (d_609_leftSucc_).PC(), 0)) if (d_609_leftSucc_).is_EState else _dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv16_, MiscTypes.Option_Some(pat_let_tv17_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv18_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]))
                return iife11_(_pat_let5_0)
            d_608_leftBranch_ = (iife10_(((xs)[numSeg]).Run(s, False)) if ((xs)[numSeg]).HasExit(False) else _dafny.SeqWithoutIsStrInference([]))
            def iife16_(_pat_let8_0):
                def iife17_(d_613_rightSucc_):
                    def iife18_(_pat_let9_0):
                        def iife19_(d_614_nextSeg_):
                            def iife20_(_pat_let10_0):
                                def iife21_(d_615_gright_):
                                    return CFGraph.BoolCFGraph.AddEdge(d_615_gright_, CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv24_, MiscTypes.Option_Some(pat_let_tv25_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv26_) + (_dafny.SeqWithoutIsStrInference([True])), d_614_nextSeg_)))
                                return iife21_(_pat_let10_0)
                            return (iife20_(default__.BuildCFGV4(pat_let_tv20_, (pat_let_tv21_) - (1), (d_614_nextSeg_).v, d_613_rightSucc_, pat_let_tv22_, (pat_let_tv23_) + (_dafny.SeqWithoutIsStrInference([True])))) if (d_614_nextSeg_).is_Some else _dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv27_, MiscTypes.Option_Some(pat_let_tv28_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv29_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]))
                        return iife19_(_pat_let9_0)
                    return (iife18_(default__.PCToSeg(pat_let_tv19_, (d_613_rightSucc_).PC(), 0)) if (d_613_rightSucc_).is_EState else _dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv30_, MiscTypes.Option_Some(pat_let_tv31_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv32_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]))
                return iife17_(_pat_let8_0)
            d_612_rightBranch_ = (iife16_(((xs)[numSeg]).Run(s, True)) if ((xs)[numSeg]).HasExit(True) else _dafny.SeqWithoutIsStrInference([]))
            return ((d_608_leftBranch_)) + ((d_612_rightBranch_))

    @staticmethod
    def PCToSeg(xs, pc, rank):
        while True:
            with _dafny.label():
                if (rank) == (len(xs)):
                    return MiscTypes.Option_None()
                elif (((xs)[rank]).StartAddress()) == (pc):
                    return MiscTypes.Option_Some(rank)
                elif True:
                    in74_ = xs
                    in75_ = pc
                    in76_ = (rank) + (1)
                    xs = in74_
                    pc = in75_
                    rank = in76_
                    raise _dafny.TailCall()
                break

