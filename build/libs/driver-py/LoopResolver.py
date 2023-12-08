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
import ProofObjectBuilder
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
                    in141_ = xs
                    in142_ = pc
                    in143_ = s
                    in144_ = (index) + (1)
                    xs = in141_
                    pc = in142_
                    s = in143_
                    index = in144_
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
                    d_987___mcc_h0_ = source69_.v
                    d_988_v_ = d_987___mcc_h0_
                    d_989_init_ = (seenOnPath)[(d_988_v_)[1]]
                    d_990_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_988_v_)[1]::])
                    d_991_segs_ = default__.NodesToSeg(d_990_path_)
                    d_992_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_993_w1_ = LinSegments.default__.WPreSeqSegs(d_991_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_988_v_)[1]::]), d_992_tgtCond_, xs, pc)
                    if (d_993_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_988_v_)[0])
                    elif (d_993_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif default__.PreservesCond(d_993_w1_, d_991_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_988_v_)[1]::]), xs, jumpDests):
                        return MiscTypes.Option_Some((d_988_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_988_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_988_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in145_ = xs
                        in146_ = pc
                        in147_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_988_v_)[1]:len(seenOnPath):])
                        in148_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_988_v_)[1]:len(boolPath):])
                        in149_ = jumpDests
                        xs = in145_
                        pc = in146_
                        seenOnPath = in147_
                        boolPath = in148_
                        jumpDests = in149_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def PreservesCond(c, seg, exits, xs, jumpDests):
        d_994_initState_ = State.default__.BuildInitState(c, 0)
        d_995_endState_ = default__.RunAll(seg, exits, xs, d_994_initState_, jumpDests)
        if (d_995_endState_).is_EState:
            return (d_995_endState_).Sat(c)
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
                        d_996___mcc_h0_ = source70_.pc
                        d_997___mcc_h1_ = source70_.stack
                        d_998_st_ = d_997___mcc_h1_
                        d_999_p_ = d_996___mcc_h0_
                        in150_ = _dafny.SeqWithoutIsStrInference((seg)[1::])
                        in151_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                        in152_ = xs
                        in153_ = State.AState_EState(d_999_p_, d_998_st_)
                        in154_ = jumpDests
                        seg = in150_
                        exits = in151_
                        xs = in152_
                        s = in153_
                        jumpDests = in154_
                        raise _dafny.TailCall()
                    elif True:
                        d_1000___mcc_h2_ = source70_.msg
                        d_1001_m_ = d_1000___mcc_h2_
                        return State.AState_Error(d_1001_m_)
                break

    @staticmethod
    def NodesToSeg(xn):
        d_1002___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_1002___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_1002___accumulator_ = (d_1002___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in155_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in155_
                    raise _dafny.TailCall()
                break

