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
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph

# Module: BuildCFGraph

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildCFGV4(xs, maxDepth, numSeg, s, seen, seenPCs, path):
        pat_let_tv8_ = xs
        pat_let_tv9_ = path
        pat_let_tv10_ = numSeg
        pat_let_tv11_ = path
        pat_let_tv12_ = xs
        pat_let_tv13_ = maxDepth
        pat_let_tv14_ = seen
        pat_let_tv15_ = seenPCs
        pat_let_tv16_ = path
        pat_let_tv17_ = path
        pat_let_tv18_ = numSeg
        pat_let_tv19_ = path
        pat_let_tv20_ = path
        pat_let_tv21_ = numSeg
        pat_let_tv22_ = path
        pat_let_tv23_ = xs
        pat_let_tv24_ = path
        pat_let_tv25_ = numSeg
        pat_let_tv26_ = path
        pat_let_tv27_ = xs
        pat_let_tv28_ = maxDepth
        pat_let_tv29_ = seen
        pat_let_tv30_ = seenPCs
        pat_let_tv31_ = path
        pat_let_tv32_ = seenPCs
        pat_let_tv33_ = path
        pat_let_tv34_ = numSeg
        pat_let_tv35_ = path
        pat_let_tv36_ = path
        pat_let_tv37_ = numSeg
        pat_let_tv38_ = xs
        pat_let_tv39_ = xs
        pat_let_tv40_ = seen
        pat_let_tv41_ = path
        pat_let_tv42_ = path
        pat_let_tv43_ = numSeg
        pat_let_tv44_ = path
        pat_let_tv45_ = path
        pat_let_tv46_ = numSeg
        pat_let_tv47_ = path
        if (maxDepth) == (0):
            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(path, MiscTypes.Option_Some(numSeg)), True, CFGraph.CFGNode_CFGNode(path, MiscTypes.Option_Some(numSeg)))]), (len(xs)) - (1))
        elif (not(((xs)[numSeg]).HasExit(False))) and (not(((xs)[numSeg]).HasExit(True))):
            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0)
        elif True:
            def iife29_(_pat_let14_0):
                def iife30_(d_743_leftSucc_):
                    def iife31_(_pat_let15_0):
                        def iife32_(d_744_nextSeg_):
                            def iife33_(_pat_let16_0):
                                def iife34_(d_745_src_):
                                    def iife35_(_pat_let17_0):
                                        def iife36_(d_746_tgt_):
                                            def iife37_(_pat_let18_0):
                                                def iife38_(d_747_gleft_):
                                                    return (d_747_gleft_).AddEdge(CFGraph.BoolEdge_BoolEdge(d_745_src_, False, d_746_tgt_))
                                                return iife38_(_pat_let18_0)
                                            return iife37_(default__.BuildCFGV4(pat_let_tv12_, (pat_let_tv13_) - (1), (d_744_nextSeg_).v, d_743_leftSucc_, (pat_let_tv14_) + (_dafny.SeqWithoutIsStrInference([d_746_tgt_])), (pat_let_tv15_) + (_dafny.SeqWithoutIsStrInference([(d_743_leftSucc_).PC()])), (pat_let_tv16_) + (_dafny.SeqWithoutIsStrInference([False]))))
                                        return iife36_(_pat_let17_0)
                                    return iife35_(CFGraph.CFGNode_CFGNode((pat_let_tv11_) + (_dafny.SeqWithoutIsStrInference([False])), d_744_nextSeg_))
                                return iife34_(_pat_let16_0)
                            return (iife33_(CFGraph.CFGNode_CFGNode(pat_let_tv9_, MiscTypes.Option_Some(pat_let_tv10_))) if (d_744_nextSeg_).is_Some else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv17_, MiscTypes.Option_Some(pat_let_tv18_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv19_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0))
                        return iife32_(_pat_let15_0)
                    return (iife31_(default__.PCToSeg(pat_let_tv8_, (d_743_leftSucc_).PC(), 0)) if ((d_743_leftSucc_).is_EState) and (((d_743_leftSucc_).PC()) < (Int.default__.TWO__256)) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv20_, MiscTypes.Option_Some(pat_let_tv21_)), False, CFGraph.CFGNode_CFGNode((pat_let_tv22_) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0))
                return iife30_(_pat_let14_0)
            d_742_leftBranch_ = (iife29_(((xs)[numSeg]).Run(s, False)) if ((xs)[numSeg]).HasExit(False) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0))
            def iife39_(_pat_let19_0):
                def iife40_(d_749_rightSucc_):
                    def iife41_(_pat_let20_0):
                        def iife42_(d_750_nextSeg_):
                            def iife43_(_pat_let21_0):
                                def iife44_(d_751_src_):
                                    def iife45_(_pat_let22_0):
                                        def iife46_(d_752_tgt_):
                                            def iife47_(_pat_let23_0):
                                                def iife48_(d_753_gright_):
                                                    return (d_753_gright_).AddEdge(CFGraph.BoolEdge_BoolEdge(d_751_src_, True, d_752_tgt_))
                                                return iife48_(_pat_let23_0)
                                            return iife47_(default__.BuildCFGV4(pat_let_tv27_, (pat_let_tv28_) - (1), (d_750_nextSeg_).v, d_749_rightSucc_, (pat_let_tv29_) + (_dafny.SeqWithoutIsStrInference([d_752_tgt_])), (pat_let_tv30_) + (_dafny.SeqWithoutIsStrInference([(d_749_rightSucc_).PC()])), (pat_let_tv31_) + (_dafny.SeqWithoutIsStrInference([True]))))
                                        return iife46_(_pat_let22_0)
                                    return iife45_(CFGraph.CFGNode_CFGNode((pat_let_tv26_) + (_dafny.SeqWithoutIsStrInference([True])), d_750_nextSeg_))
                                return iife44_(_pat_let21_0)
                            def lambda42_(source59_):
                                if source59_.is_None:
                                    return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv33_, MiscTypes.Option_Some(pat_let_tv34_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv35_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0)
                                elif True:
                                    d_754___mcc_h0_ = source59_.v
                                    def iife49_(_pat_let24_0):
                                        def iife50_(d_755_prev_):
                                            return CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv36_, MiscTypes.Option_Some(pat_let_tv37_)), True, d_755_prev_)]), len(pat_let_tv38_))
                                        return iife50_(_pat_let24_0)
                                    return iife49_(d_754___mcc_h0_)

                            return ((iife43_(CFGraph.CFGNode_CFGNode(pat_let_tv24_, MiscTypes.Option_Some(pat_let_tv25_))) if ((d_749_rightSucc_).PC()) not in (pat_let_tv32_) else lambda42_(default__.SafeLoopFound(pat_let_tv39_, (d_749_rightSucc_).PC(), pat_let_tv40_, pat_let_tv41_))) if (d_750_nextSeg_).is_Some else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv42_, MiscTypes.Option_Some(pat_let_tv43_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv44_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0))
                        return iife42_(_pat_let20_0)
                    return (iife41_(default__.PCToSeg(pat_let_tv23_, (d_749_rightSucc_).PC(), 0)) if ((d_749_rightSucc_).is_EState) and (((d_749_rightSucc_).PC()) < (Int.default__.TWO__256)) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode(pat_let_tv45_, MiscTypes.Option_Some(pat_let_tv46_)), True, CFGraph.CFGNode_CFGNode((pat_let_tv47_) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0))
                return iife40_(_pat_let19_0)
            d_748_rightBranch_ = (iife39_(((xs)[numSeg]).Run(s, True)) if ((xs)[numSeg]).HasExit(True) else CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0))
            return CFGraph.BoolCFGraph_BoolCFGraph(((d_742_leftBranch_).edges) + ((d_748_rightBranch_).edges), (len(xs)) - (1))

    @staticmethod
    def PCToSeg(xs, pc, rank):
        while True:
            with _dafny.label():
                if (rank) == (len(xs)):
                    return MiscTypes.Option_None()
                elif (((xs)[rank]).StartAddress()) == (pc):
                    return MiscTypes.Option_Some(rank)
                elif True:
                    in115_ = xs
                    in116_ = pc
                    in117_ = (rank) + (1)
                    xs = in115_
                    pc = in116_
                    rank = in117_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def FindFirstNodeWithPC(xs, pc, s, index):
        while True:
            with _dafny.label():
                if (len(s)) == (index):
                    return MiscTypes.Option_None()
                elif ((((s)[index]).seg).is_Some) and ((((xs)[(((s)[index]).seg).v]).StartAddress()) == (pc)):
                    return MiscTypes.Option_Some(((s)[index], index))
                elif True:
                    in118_ = xs
                    in119_ = pc
                    in120_ = s
                    in121_ = (index) + (1)
                    xs = in118_
                    pc = in119_
                    s = in120_
                    index = in121_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SafeLoopFound(xs, pc, seenOnPath, path):
        source60_ = default__.FindFirstNodeWithPC(xs, pc, seenOnPath, 0)
        if source60_.is_None:
            return MiscTypes.Option_None()
        elif True:
            d_756___mcc_h0_ = source60_.v
            d_757_v_ = d_756___mcc_h0_
            d_758_init_ = (seenOnPath)[(d_757_v_)[1]]
            d_759_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_757_v_)[1]::])
            d_760_segs_ = default__.NodesToSeg(d_759_path_, xs)
            d_761_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc)
            d_762_w1_ = LinSegments.default__.WPreSeqSegs(d_760_segs_, d_761_tgtCond_, xs)
            if (d_762_w1_).is_StTrue:
                return MiscTypes.Option_Some((d_757_v_)[0])
            elif True:
                return MiscTypes.Option_None()

    @staticmethod
    def NodesToSeg(xn, xs):
        d_763___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_763___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_763___accumulator_ = (d_763___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in122_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    in123_ = xs
                    xn = in122_
                    xs = in123_
                    raise _dafny.TailCall()
                break

