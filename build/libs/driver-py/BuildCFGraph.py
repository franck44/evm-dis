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
    def BuildCFGV5(xs, maxDepth, jumpDests, numSeg, s, seen, seenPCs, path, seenStates):
        pat_let_tv2_ = path
        pat_let_tv3_ = numSeg
        pat_let_tv4_ = seenStates
        pat_let_tv5_ = seenStates
        pat_let_tv6_ = seenStates
        pat_let_tv7_ = xs
        pat_let_tv8_ = path
        pat_let_tv9_ = numSeg
        pat_let_tv10_ = path
        pat_let_tv11_ = seenStates
        pat_let_tv12_ = xs
        pat_let_tv13_ = maxDepth
        pat_let_tv14_ = jumpDests
        pat_let_tv15_ = seen
        pat_let_tv16_ = seenPCs
        pat_let_tv17_ = path
        pat_let_tv18_ = path
        pat_let_tv19_ = numSeg
        pat_let_tv20_ = path
        pat_let_tv21_ = seenStates
        pat_let_tv22_ = path
        pat_let_tv23_ = numSeg
        pat_let_tv24_ = path
        pat_let_tv25_ = seenStates
        pat_let_tv26_ = xs
        pat_let_tv27_ = path
        pat_let_tv28_ = numSeg
        pat_let_tv29_ = path
        pat_let_tv30_ = numSeg
        pat_let_tv31_ = path
        pat_let_tv32_ = xs
        pat_let_tv33_ = maxDepth
        pat_let_tv34_ = jumpDests
        pat_let_tv35_ = seen
        pat_let_tv36_ = seenPCs
        pat_let_tv37_ = path
        pat_let_tv38_ = seenPCs
        pat_let_tv39_ = path
        pat_let_tv40_ = numSeg
        pat_let_tv41_ = path
        pat_let_tv42_ = xs
        pat_let_tv43_ = maxDepth
        pat_let_tv44_ = jumpDests
        pat_let_tv45_ = seen
        pat_let_tv46_ = seenPCs
        pat_let_tv47_ = path
        pat_let_tv48_ = path
        pat_let_tv49_ = numSeg
        pat_let_tv50_ = xs
        pat_let_tv51_ = xs
        pat_let_tv52_ = seen
        pat_let_tv53_ = path
        pat_let_tv54_ = jumpDests
        pat_let_tv55_ = path
        pat_let_tv56_ = numSeg
        pat_let_tv57_ = path
        pat_let_tv58_ = path
        pat_let_tv59_ = numSeg
        pat_let_tv60_ = path
        if (not(((xs)[numSeg]).HasExit(False))) and (not(((xs)[numSeg]).HasExit(True))):
            return (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), seenStates)
        elif (maxDepth) == (0):
            return (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(path, MiscTypes.Option_Some(numSeg)), True, CFGraph.CFGNode_CFGNode(path, MiscTypes.Option_Some(numSeg)))]), (len(xs)) - (1)), seenStates)
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
                                                def iife46_(d_984_newSeenSegs_):
                                                    def iife47_(_pat_let23_0):
                                                        def iife48_(d_985_gleft_):
                                                            return (((d_985_gleft_)[0]).AddEdge(CFGraph.BoolEdge_BoolEdge(d_982_src_, False, d_983_tgt_)), (d_985_gleft_)[1])
                                                        return iife48_(_pat_let23_0)
                                                    return iife47_(default__.BuildCFGV5(pat_let_tv12_, (pat_let_tv13_) - (1), pat_let_tv14_, (d_981_nextSeg_).v, d_980_leftSucc_, (pat_let_tv15_) + (_dafny.SeqWithoutIsStrInference([d_983_tgt_])), (pat_let_tv16_) + (_dafny.SeqWithoutIsStrInference([(d_980_leftSucc_).PC()])), (pat_let_tv17_) + (_dafny.SeqWithoutIsStrInference([False])), d_984_newSeenSegs_))
                                                return iife46_(_pat_let22_0)
                                            return iife45_((pat_let_tv11_).set(d_980_leftSucc_, d_983_tgt_))
                                        return iife44_(_pat_let21_0)
                                    return iife43_(CFGraph.CFGNode_CFGNode((pat_let_tv10_) + (_dafny.SeqWithoutIsStrInference([False])), d_981_nextSeg_))
                                return iife42_(_pat_let20_0)
                            return (iife41_(CFGraph.CFGNode_CFGNode(pat_let_tv8_, MiscTypes.Option_Some(pat_let_tv9_))) if (d_981_nextSeg_).is_Some else (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv18_, MiscTypes.Option_Some(pat_let_tv19_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv20_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0), pat_let_tv21_))
                        return iife40_(_pat_let19_0)
                    return ((CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv2_, MiscTypes.Option_Some(pat_let_tv3_)), False, (pat_let_tv4_)[d_980_leftSucc_])]), 0), pat_let_tv5_) if (d_980_leftSucc_) in (pat_let_tv6_) else (iife39_(LinSegments.default__.PCToSeg(pat_let_tv7_, (d_980_leftSucc_).PC(), 0)) if ((d_980_leftSucc_).is_EState) and (((d_980_leftSucc_).PC()) < (Int.default__.TWO__256)) else (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv22_, MiscTypes.Option_Some(pat_let_tv23_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv24_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0), pat_let_tv25_)))
                return iife38_(_pat_let18_0)
            d_979_leftBranch_ = (iife37_(((xs)[numSeg]).Run(s, False, jumpDests)) if ((xs)[numSeg]).HasExit(False) else (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), seenStates))
            d_986_newSeenStates_ = (d_979_leftBranch_)[1]
            def iife49_(_pat_let24_0):
                def iife50_(d_988_rightSucc_):
                    def iife51_(_pat_let25_0):
                        def iife52_(d_989_nextSeg_):
                            def iife53_(_pat_let26_0):
                                def iife54_(d_990_src_):
                                    def iife55_(_pat_let27_0):
                                        def iife56_(d_991_tgt_):
                                            def iife57_(_pat_let28_0):
                                                def iife58_(d_992_newSeenSegs_):
                                                    def iife59_(_pat_let29_0):
                                                        def iife60_(d_993_gright_):
                                                            return (((d_993_gright_)[0]).AddEdge(CFGraph.BoolEdge_BoolEdge(d_990_src_, True, d_991_tgt_)), (d_993_gright_)[1])
                                                        return iife60_(_pat_let29_0)
                                                    return iife59_(default__.BuildCFGV5(pat_let_tv32_, (pat_let_tv33_) - (1), pat_let_tv34_, (d_989_nextSeg_).v, d_988_rightSucc_, (pat_let_tv35_) + (_dafny.SeqWithoutIsStrInference([d_991_tgt_])), (pat_let_tv36_) + (_dafny.SeqWithoutIsStrInference([(d_988_rightSucc_).PC()])), (pat_let_tv37_) + (_dafny.SeqWithoutIsStrInference([True])), d_992_newSeenSegs_))
                                                return iife58_(_pat_let28_0)
                                            return iife57_((d_986_newSeenStates_).set(d_988_rightSucc_, d_991_tgt_))
                                        return iife56_(_pat_let27_0)
                                    return iife55_(CFGraph.CFGNode_CFGNode((pat_let_tv31_) + (_dafny.SeqWithoutIsStrInference([True])), d_989_nextSeg_))
                                return iife54_(_pat_let26_0)
                            def lambda59_(source71_):
                                if source71_.is_None:
                                    def iife61_(_pat_let30_0):
                                        def iife62_(d_994_src_):
                                            def iife63_(_pat_let31_0):
                                                def iife64_(d_995_tgt_):
                                                    def iife65_(_pat_let32_0):
                                                        def iife66_(d_996_newSeenSegs_):
                                                            def iife67_(_pat_let33_0):
                                                                def iife68_(d_997_gright_):
                                                                    return (((d_997_gright_)[0]).AddEdge(CFGraph.BoolEdge_BoolEdge(d_994_src_, True, d_995_tgt_)), (d_997_gright_)[1])
                                                                return iife68_(_pat_let33_0)
                                                            return iife67_(default__.BuildCFGV5(pat_let_tv42_, (pat_let_tv43_) - (1), pat_let_tv44_, (d_989_nextSeg_).v, d_988_rightSucc_, (pat_let_tv45_) + (_dafny.SeqWithoutIsStrInference([d_995_tgt_])), (pat_let_tv46_) + (_dafny.SeqWithoutIsStrInference([(d_988_rightSucc_).PC()])), (pat_let_tv47_) + (_dafny.SeqWithoutIsStrInference([True])), d_996_newSeenSegs_))
                                                        return iife66_(_pat_let32_0)
                                                    return iife65_((d_986_newSeenStates_).set(d_988_rightSucc_, d_995_tgt_))
                                                return iife64_(_pat_let31_0)
                                            return iife63_(CFGraph.CFGNode_CFGNode((pat_let_tv41_) + (_dafny.SeqWithoutIsStrInference([True])), d_989_nextSeg_))
                                        return iife62_(_pat_let30_0)
                                    return iife61_(CFGraph.CFGNode_CFGNode(pat_let_tv39_, MiscTypes.Option_Some(pat_let_tv40_)))
                                elif True:
                                    d_998___mcc_h0_ = source71_.v
                                    def iife69_(_pat_let34_0):
                                        def iife70_(d_999_prev_):
                                            return (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv48_, MiscTypes.Option_Some(pat_let_tv49_)), True, d_999_prev_)]), len(pat_let_tv50_)), d_986_newSeenStates_)
                                        return iife70_(_pat_let34_0)
                                    return iife69_(d_998___mcc_h0_)

                            return (((CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv27_, MiscTypes.Option_Some(pat_let_tv28_)), True, (d_986_newSeenStates_)[d_988_rightSucc_])]), 0), d_986_newSeenStates_) if (d_988_rightSucc_) in (d_986_newSeenStates_) else (iife53_(CFGraph.CFGNode_CFGNode(pat_let_tv29_, MiscTypes.Option_Some(pat_let_tv30_))) if ((d_988_rightSucc_).PC()) not in (pat_let_tv38_) else lambda59_(LoopResolver.default__.SafeLoopFound(pat_let_tv51_, (d_988_rightSucc_).PC(), pat_let_tv52_, (pat_let_tv53_) + (_dafny.SeqWithoutIsStrInference([True])), pat_let_tv54_)))) if (d_989_nextSeg_).is_Some else (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv55_, MiscTypes.Option_Some(pat_let_tv56_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv57_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0), d_986_newSeenStates_))
                        return iife52_(_pat_let25_0)
                    return (iife51_(LinSegments.default__.PCToSeg(pat_let_tv26_, (d_988_rightSucc_).PC(), 0)) if ((d_988_rightSucc_).is_EState) and (((d_988_rightSucc_).PC()) < (Int.default__.TWO__256)) else (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv58_, MiscTypes.Option_Some(pat_let_tv59_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv60_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0), d_986_newSeenStates_))
                return iife50_(_pat_let24_0)
            d_987_rightBranch_ = (iife49_(((xs)[numSeg]).Run(s, True, jumpDests)) if ((xs)[numSeg]).HasExit(True) else (CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), d_986_newSeenStates_))
            return (CFGraph.BoolCFGraph_BoolCFGraph((((d_979_leftBranch_)[0]).edges) + (((d_987_rightBranch_)[0]).edges), (len(xs)) - (1)), (d_987_rightBranch_)[1])

