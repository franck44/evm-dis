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
    def BuildCFGV4(xs, maxDepth, numSeg, s, seen, seenPCs, path):
        pat_let_tv2_ = xs
        pat_let_tv3_ = path
        pat_let_tv4_ = numSeg
        pat_let_tv5_ = path
        pat_let_tv6_ = xs
        pat_let_tv7_ = maxDepth
        pat_let_tv8_ = seen
        pat_let_tv9_ = seenPCs
        pat_let_tv10_ = path
        pat_let_tv11_ = path
        pat_let_tv12_ = numSeg
        pat_let_tv13_ = path
        pat_let_tv14_ = path
        pat_let_tv15_ = numSeg
        pat_let_tv16_ = path
        pat_let_tv17_ = xs
        pat_let_tv18_ = path
        pat_let_tv19_ = numSeg
        pat_let_tv20_ = path
        pat_let_tv21_ = xs
        pat_let_tv22_ = maxDepth
        pat_let_tv23_ = seen
        pat_let_tv24_ = seenPCs
        pat_let_tv25_ = path
        pat_let_tv26_ = seenPCs
        pat_let_tv27_ = path
        pat_let_tv28_ = numSeg
        pat_let_tv29_ = path
        pat_let_tv30_ = xs
        pat_let_tv31_ = maxDepth
        pat_let_tv32_ = seen
        pat_let_tv33_ = seenPCs
        pat_let_tv34_ = path
        pat_let_tv35_ = path
        pat_let_tv36_ = numSeg
        pat_let_tv37_ = xs
        pat_let_tv38_ = xs
        pat_let_tv39_ = seen
        pat_let_tv40_ = path
        pat_let_tv41_ = path
        pat_let_tv42_ = numSeg
        pat_let_tv43_ = path
        pat_let_tv44_ = path
        pat_let_tv45_ = numSeg
        pat_let_tv46_ = path
        if (maxDepth) == (0):
            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(path, MiscTypes.Option_Some(numSeg)), True, CFGraph.CFGNode_CFGNode(path, MiscTypes.Option_Some(numSeg)))]), (len(xs)) - (1))
        elif (not(((xs)[numSeg]).HasExit(False))) and (not(((xs)[numSeg]).HasExit(True))):
            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0)
        elif True:
            def iife17_(_pat_let8_0):
                def iife18_(d_796_leftSucc_):
                    def iife19_(_pat_let9_0):
                        def iife20_(d_797_nextSeg_):
                            def iife21_(_pat_let10_0):
                                def iife22_(d_798_src_):
                                    def iife23_(_pat_let11_0):
                                        def iife24_(d_799_tgt_):
                                            def iife25_(_pat_let12_0):
                                                def iife26_(d_800_gleft_):
                                                    return (d_800_gleft_).AddEdge(CFGraph.BoolEdge_BoolEdge(d_798_src_, False, d_799_tgt_))
                                                return iife26_(_pat_let12_0)
                                            return iife25_(default__.BuildCFGV4(pat_let_tv6_, (pat_let_tv7_) - (1), (d_797_nextSeg_).v, d_796_leftSucc_, (pat_let_tv8_) + (_dafny.SeqWithoutIsStrInference([d_799_tgt_])), (pat_let_tv9_) + (_dafny.SeqWithoutIsStrInference([(d_796_leftSucc_).PC()])), (pat_let_tv10_) + (_dafny.SeqWithoutIsStrInference([False]))))
                                        return iife24_(_pat_let11_0)
                                    return iife23_(CFGraph.CFGNode_CFGNode((pat_let_tv5_) + (_dafny.SeqWithoutIsStrInference([False])), d_797_nextSeg_))
                                return iife22_(_pat_let10_0)
                            return (iife21_(CFGraph.CFGNode_CFGNode(pat_let_tv3_, MiscTypes.Option_Some(pat_let_tv4_))) if (d_797_nextSeg_).is_Some else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv11_, MiscTypes.Option_Some(pat_let_tv12_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv13_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0))
                        return iife20_(_pat_let9_0)
                    return (iife19_(LinSegments.default__.PCToSeg(pat_let_tv2_, (d_796_leftSucc_).PC(), 0)) if ((d_796_leftSucc_).is_EState) and (((d_796_leftSucc_).PC()) < (Int.default__.TWO__256)) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv14_, MiscTypes.Option_Some(pat_let_tv15_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv16_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0))
                return iife18_(_pat_let8_0)
            d_795_leftBranch_ = (iife17_(((xs)[numSeg]).Run(s, False)) if ((xs)[numSeg]).HasExit(False) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0))
            def iife27_(_pat_let13_0):
                def iife28_(d_802_rightSucc_):
                    def iife29_(_pat_let14_0):
                        def iife30_(d_803_nextSeg_):
                            def iife31_(_pat_let15_0):
                                def iife32_(d_804_src_):
                                    def iife33_(_pat_let16_0):
                                        def iife34_(d_805_tgt_):
                                            def iife35_(_pat_let17_0):
                                                def iife36_(d_806_gright_):
                                                    return (d_806_gright_).AddEdge(CFGraph.BoolEdge_BoolEdge(d_804_src_, True, d_805_tgt_))
                                                return iife36_(_pat_let17_0)
                                            return iife35_(default__.BuildCFGV4(pat_let_tv21_, (pat_let_tv22_) - (1), (d_803_nextSeg_).v, d_802_rightSucc_, (pat_let_tv23_) + (_dafny.SeqWithoutIsStrInference([d_805_tgt_])), (pat_let_tv24_) + (_dafny.SeqWithoutIsStrInference([(d_802_rightSucc_).PC()])), (pat_let_tv25_) + (_dafny.SeqWithoutIsStrInference([True]))))
                                        return iife34_(_pat_let16_0)
                                    return iife33_(CFGraph.CFGNode_CFGNode((pat_let_tv20_) + (_dafny.SeqWithoutIsStrInference([True])), d_803_nextSeg_))
                                return iife32_(_pat_let15_0)
                            def lambda40_(source66_):
                                if source66_.is_None:
                                    def iife37_(_pat_let18_0):
                                        def iife38_(d_807_src_):
                                            def iife39_(_pat_let19_0):
                                                def iife40_(d_808_tgt_):
                                                    def iife41_(_pat_let20_0):
                                                        def iife42_(d_809_gright_):
                                                            return (d_809_gright_).AddEdge(CFGraph.BoolEdge_BoolEdge(d_807_src_, True, d_808_tgt_))
                                                        return iife42_(_pat_let20_0)
                                                    return iife41_(default__.BuildCFGV4(pat_let_tv30_, (pat_let_tv31_) - (1), (d_803_nextSeg_).v, d_802_rightSucc_, (pat_let_tv32_) + (_dafny.SeqWithoutIsStrInference([d_808_tgt_])), (pat_let_tv33_) + (_dafny.SeqWithoutIsStrInference([(d_802_rightSucc_).PC()])), (pat_let_tv34_) + (_dafny.SeqWithoutIsStrInference([True]))))
                                                return iife40_(_pat_let19_0)
                                            return iife39_(CFGraph.CFGNode_CFGNode((pat_let_tv29_) + (_dafny.SeqWithoutIsStrInference([True])), d_803_nextSeg_))
                                        return iife38_(_pat_let18_0)
                                    return iife37_(CFGraph.CFGNode_CFGNode(pat_let_tv27_, MiscTypes.Option_Some(pat_let_tv28_)))
                                elif True:
                                    d_810___mcc_h0_ = source66_.v
                                    def iife43_(_pat_let21_0):
                                        def iife44_(d_811_prev_):
                                            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv35_, MiscTypes.Option_Some(pat_let_tv36_)), True, d_811_prev_)]), len(pat_let_tv37_))
                                        return iife44_(_pat_let21_0)
                                    return iife43_(d_810___mcc_h0_)

                            return ((iife31_(CFGraph.CFGNode_CFGNode(pat_let_tv18_, MiscTypes.Option_Some(pat_let_tv19_))) if ((d_802_rightSucc_).PC()) not in (pat_let_tv26_) else lambda40_(LoopResolver.default__.SafeLoopFound(pat_let_tv38_, (d_802_rightSucc_).PC(), pat_let_tv39_, (pat_let_tv40_) + (_dafny.SeqWithoutIsStrInference([True]))))) if (d_803_nextSeg_).is_Some else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv41_, MiscTypes.Option_Some(pat_let_tv42_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv43_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0))
                        return iife30_(_pat_let14_0)
                    return (iife29_(LinSegments.default__.PCToSeg(pat_let_tv17_, (d_802_rightSucc_).PC(), 0)) if ((d_802_rightSucc_).is_EState) and (((d_802_rightSucc_).PC()) < (Int.default__.TWO__256)) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv44_, MiscTypes.Option_Some(pat_let_tv45_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv46_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0))
                return iife28_(_pat_let13_0)
            d_801_rightBranch_ = (iife27_(((xs)[numSeg]).Run(s, True)) if ((xs)[numSeg]).HasExit(True) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0))
            return CFGraph.BoolCFGraph_BoolCFGraph(((d_795_leftBranch_).edges) + ((d_801_rightBranch_).edges), (len(xs)) - (1))

