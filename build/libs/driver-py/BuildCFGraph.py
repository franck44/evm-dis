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
import ProofObjectBuilder
import ArgParser
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph
import LoopResolver

# Module: BuildCFGraph

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildCFGV4(xs, maxDepth, jumpDests, numSeg, s, seen, seenPCs, path):
        pat_let_tv2_ = xs
        pat_let_tv3_ = path
        pat_let_tv4_ = numSeg
        pat_let_tv5_ = path
        pat_let_tv6_ = xs
        pat_let_tv7_ = maxDepth
        pat_let_tv8_ = jumpDests
        pat_let_tv9_ = seen
        pat_let_tv10_ = seenPCs
        pat_let_tv11_ = path
        pat_let_tv12_ = path
        pat_let_tv13_ = numSeg
        pat_let_tv14_ = path
        pat_let_tv15_ = path
        pat_let_tv16_ = numSeg
        pat_let_tv17_ = path
        pat_let_tv18_ = xs
        pat_let_tv19_ = path
        pat_let_tv20_ = numSeg
        pat_let_tv21_ = path
        pat_let_tv22_ = xs
        pat_let_tv23_ = maxDepth
        pat_let_tv24_ = jumpDests
        pat_let_tv25_ = seen
        pat_let_tv26_ = seenPCs
        pat_let_tv27_ = path
        pat_let_tv28_ = seenPCs
        pat_let_tv29_ = path
        pat_let_tv30_ = numSeg
        pat_let_tv31_ = path
        pat_let_tv32_ = xs
        pat_let_tv33_ = maxDepth
        pat_let_tv34_ = jumpDests
        pat_let_tv35_ = seen
        pat_let_tv36_ = seenPCs
        pat_let_tv37_ = path
        pat_let_tv38_ = path
        pat_let_tv39_ = numSeg
        pat_let_tv40_ = xs
        pat_let_tv41_ = xs
        pat_let_tv42_ = seen
        pat_let_tv43_ = path
        pat_let_tv44_ = jumpDests
        pat_let_tv45_ = path
        pat_let_tv46_ = numSeg
        pat_let_tv47_ = path
        pat_let_tv48_ = path
        pat_let_tv49_ = numSeg
        pat_let_tv50_ = path
        if (not(((xs)[numSeg]).HasExit(False))) and (not(((xs)[numSeg]).HasExit(True))):
            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0)
        elif (maxDepth) == (0):
            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(path, MiscTypes.Option_Some(numSeg)), True, CFGraph.CFGNode_CFGNode(path, MiscTypes.Option_Some(numSeg)))]), (len(xs)) - (1))
        elif True:
            def iife37_(_pat_let18_0):
                def iife38_(d_980_leftSucc_):
                    def iife39_(_pat_let19_0):
                        def iife40_(d_981_nextSeg_):
                            def iife41_(_pat_let20_0):
                                def iife42_(d_982_src_):
                                    def iife43_(_pat_let21_0):
                                        def iife44_(d_983_tgt_):
                                            def iife45_(_pat_let22_0):
                                                def iife46_(d_984_gleft_):
                                                    return (d_984_gleft_).AddEdge(CFGraph.BoolEdge_BoolEdge(d_982_src_, False, d_983_tgt_))
                                                return iife46_(_pat_let22_0)
                                            return iife45_(default__.BuildCFGV4(pat_let_tv6_, (pat_let_tv7_) - (1), pat_let_tv8_, (d_981_nextSeg_).v, d_980_leftSucc_, (pat_let_tv9_) + (_dafny.SeqWithoutIsStrInference([d_983_tgt_])), (pat_let_tv10_) + (_dafny.SeqWithoutIsStrInference([(d_980_leftSucc_).PC()])), (pat_let_tv11_) + (_dafny.SeqWithoutIsStrInference([False]))))
                                        return iife44_(_pat_let21_0)
                                    return iife43_(CFGraph.CFGNode_CFGNode((pat_let_tv5_) + (_dafny.SeqWithoutIsStrInference([False])), d_981_nextSeg_))
                                return iife42_(_pat_let20_0)
                            return (iife41_(CFGraph.CFGNode_CFGNode(pat_let_tv3_, MiscTypes.Option_Some(pat_let_tv4_))) if (d_981_nextSeg_).is_Some else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv12_, MiscTypes.Option_Some(pat_let_tv13_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv14_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0))
                        return iife40_(_pat_let19_0)
                    return (iife39_(LinSegments.default__.PCToSeg(pat_let_tv2_, (d_980_leftSucc_).PC(), 0)) if ((d_980_leftSucc_).is_EState) and (((d_980_leftSucc_).PC()) < (Int.default__.TWO__256)) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv15_, MiscTypes.Option_Some(pat_let_tv16_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv17_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0))
                return iife38_(_pat_let18_0)
            d_979_leftBranch_ = (iife37_(((xs)[numSeg]).Run(s, False, jumpDests)) if ((xs)[numSeg]).HasExit(False) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0))
            def iife47_(_pat_let23_0):
                def iife48_(d_986_rightSucc_):
                    def iife49_(_pat_let24_0):
                        def iife50_(d_987_nextSeg_):
                            def iife51_(_pat_let25_0):
                                def iife52_(d_988_src_):
                                    def iife53_(_pat_let26_0):
                                        def iife54_(d_989_tgt_):
                                            def iife55_(_pat_let27_0):
                                                def iife56_(d_990_gright_):
                                                    return (d_990_gright_).AddEdge(CFGraph.BoolEdge_BoolEdge(d_988_src_, True, d_989_tgt_))
                                                return iife56_(_pat_let27_0)
                                            return iife55_(default__.BuildCFGV4(pat_let_tv22_, (pat_let_tv23_) - (1), pat_let_tv24_, (d_987_nextSeg_).v, d_986_rightSucc_, (pat_let_tv25_) + (_dafny.SeqWithoutIsStrInference([d_989_tgt_])), (pat_let_tv26_) + (_dafny.SeqWithoutIsStrInference([(d_986_rightSucc_).PC()])), (pat_let_tv27_) + (_dafny.SeqWithoutIsStrInference([True]))))
                                        return iife54_(_pat_let26_0)
                                    return iife53_(CFGraph.CFGNode_CFGNode((pat_let_tv21_) + (_dafny.SeqWithoutIsStrInference([True])), d_987_nextSeg_))
                                return iife52_(_pat_let25_0)
                            def lambda59_(source71_):
                                if source71_.is_None:
                                    def iife57_(_pat_let28_0):
                                        def iife58_(d_991_src_):
                                            def iife59_(_pat_let29_0):
                                                def iife60_(d_992_tgt_):
                                                    def iife61_(_pat_let30_0):
                                                        def iife62_(d_993_gright_):
                                                            return (d_993_gright_).AddEdge(CFGraph.BoolEdge_BoolEdge(d_991_src_, True, d_992_tgt_))
                                                        return iife62_(_pat_let30_0)
                                                    return iife61_(default__.BuildCFGV4(pat_let_tv32_, (pat_let_tv33_) - (1), pat_let_tv34_, (d_987_nextSeg_).v, d_986_rightSucc_, (pat_let_tv35_) + (_dafny.SeqWithoutIsStrInference([d_992_tgt_])), (pat_let_tv36_) + (_dafny.SeqWithoutIsStrInference([(d_986_rightSucc_).PC()])), (pat_let_tv37_) + (_dafny.SeqWithoutIsStrInference([True]))))
                                                return iife60_(_pat_let29_0)
                                            return iife59_(CFGraph.CFGNode_CFGNode((pat_let_tv31_) + (_dafny.SeqWithoutIsStrInference([True])), d_987_nextSeg_))
                                        return iife58_(_pat_let28_0)
                                    return iife57_(CFGraph.CFGNode_CFGNode(pat_let_tv29_, MiscTypes.Option_Some(pat_let_tv30_)))
                                elif True:
                                    d_994___mcc_h0_ = source71_.v
                                    def iife63_(_pat_let31_0):
                                        def iife64_(d_995_prev_):
                                            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv38_, MiscTypes.Option_Some(pat_let_tv39_)), True, d_995_prev_)]), len(pat_let_tv40_))
                                        return iife64_(_pat_let31_0)
                                    return iife63_(d_994___mcc_h0_)

                            return ((iife51_(CFGraph.CFGNode_CFGNode(pat_let_tv19_, MiscTypes.Option_Some(pat_let_tv20_))) if ((d_986_rightSucc_).PC()) not in (pat_let_tv28_) else lambda59_(LoopResolver.default__.SafeLoopFound(pat_let_tv41_, (d_986_rightSucc_).PC(), pat_let_tv42_, (pat_let_tv43_) + (_dafny.SeqWithoutIsStrInference([True])), pat_let_tv44_))) if (d_987_nextSeg_).is_Some else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv45_, MiscTypes.Option_Some(pat_let_tv46_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv47_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0))
                        return iife50_(_pat_let24_0)
                    return (iife49_(LinSegments.default__.PCToSeg(pat_let_tv18_, (d_986_rightSucc_).PC(), 0)) if ((d_986_rightSucc_).is_EState) and (((d_986_rightSucc_).PC()) < (Int.default__.TWO__256)) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv48_, MiscTypes.Option_Some(pat_let_tv49_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv50_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0))
                return iife48_(_pat_let23_0)
            d_985_rightBranch_ = (iife47_(((xs)[numSeg]).Run(s, True, jumpDests)) if ((xs)[numSeg]).HasExit(True) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0))
            return CFGraph.BoolCFGraph_BoolCFGraph(((d_979_leftBranch_).edges) + ((d_985_rightBranch_).edges), (len(xs)) - (1))

