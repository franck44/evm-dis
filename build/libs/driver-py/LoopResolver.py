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
import EVMObject
import ArgParser
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph

# Module: LoopResolver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def FindFirstNodeWithPC(xs, pc, s, index):
        while True:
            with _dafny.label():
                if (len(s)) == (index):
                    return MiscTypes.Option_None()
                elif ((((s)[index]).seg).is_Some) and ((((xs)[(((s)[index]).seg).v]).StartAddress()) == (pc)):
                    return MiscTypes.Option_Some(((s)[index], index))
                elif True:
                    in144_ = xs
                    in145_ = pc
                    in146_ = s
                    in147_ = (index) + (1)
                    xs = in144_
                    pc = in145_
                    s = in146_
                    index = in147_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SafeLoopFound(xs, pc, seenOnPath, boolPath, jumpDests):
        while True:
            with _dafny.label():
                source69_ = default__.FindFirstNodeWithPC(xs, pc, seenOnPath, 0)
                if source69_.is_None:
                    return MiscTypes.Option_None()
                elif True:
                    d_990___mcc_h0_ = source69_.v
                    d_991_v_ = d_990___mcc_h0_
                    d_992_init_ = (seenOnPath)[(d_991_v_)[1]]
                    d_993_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_991_v_)[1]::])
                    d_994_segs_ = default__.NodesToSeg(d_993_path_)
                    d_995_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_996_w1_ = LinSegments.default__.WPreSeqSegs(d_994_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_991_v_)[1]::]), d_995_tgtCond_, xs, pc)
                    if (d_996_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_991_v_)[0])
                    elif (d_996_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif default__.PreservesCond(d_996_w1_, d_994_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_991_v_)[1]::]), xs, jumpDests):
                        return MiscTypes.Option_Some((d_991_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_991_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_991_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in148_ = xs
                        in149_ = pc
                        in150_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_991_v_)[1]:len(seenOnPath):])
                        in151_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_991_v_)[1]:len(boolPath):])
                        in152_ = jumpDests
                        xs = in148_
                        pc = in149_
                        seenOnPath = in150_
                        boolPath = in151_
                        jumpDests = in152_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def PreservesCond(c, seg, exits, xs, jumpDests):
        d_997_initState_ = State.default__.BuildInitState(c, 0)
        d_998_endState_ = default__.RunAll(seg, exits, xs, d_997_initState_, jumpDests)
        if (d_998_endState_).is_EState:
            return (d_998_endState_).Sat(c)
        elif True:
            return False

    @staticmethod
    def RunAll(seg, exits, xs, s, jumpDests):
        while True:
            with _dafny.label():
                if (len(seg)) == (0):
                    return s
                elif True:
                    source70_ = ((xs)[(seg)[0]]).Run(s, (exits)[0], jumpDests)
                    if source70_.is_EState:
                        d_999___mcc_h0_ = source70_.pc
                        d_1000___mcc_h1_ = source70_.stack
                        d_1001_st_ = d_1000___mcc_h1_
                        d_1002_p_ = d_999___mcc_h0_
                        in153_ = _dafny.SeqWithoutIsStrInference((seg)[1::])
                        in154_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                        in155_ = xs
                        in156_ = State.AState_EState(d_1002_p_, d_1001_st_)
                        in157_ = jumpDests
                        seg = in153_
                        exits = in154_
                        xs = in155_
                        s = in156_
                        jumpDests = in157_
                        raise _dafny.TailCall()
                    elif True:
                        d_1003___mcc_h2_ = source70_.msg
                        d_1004_m_ = d_1003___mcc_h2_
                        return State.AState_Error(d_1004_m_)
                break

    @staticmethod
    def NodesToSeg(xn):
        d_1005___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_1005___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_1005___accumulator_ = (d_1005___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in158_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in158_
                    raise _dafny.TailCall()
                break

