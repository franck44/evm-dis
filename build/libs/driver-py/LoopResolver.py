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
                    in132_ = xs
                    in133_ = pc
                    in134_ = s
                    in135_ = (index) + (1)
                    xs = in132_
                    pc = in133_
                    s = in134_
                    index = in135_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SafeLoopFound(xs, pc, seenOnPath, boolPath):
        while True:
            with _dafny.label():
                source67_ = default__.FindFirstNodeWithPC(xs, pc, seenOnPath, 0)
                if source67_.is_None:
                    return MiscTypes.Option_None()
                elif True:
                    d_926___mcc_h0_ = source67_.v
                    d_927_v_ = d_926___mcc_h0_
                    d_928_init_ = (seenOnPath)[(d_927_v_)[1]]
                    d_929_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_927_v_)[1]::])
                    d_930_segs_ = default__.NodesToSeg(d_929_path_)
                    d_931_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_932_w1_ = LinSegments.default__.WPreSeqSegs(d_930_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_927_v_)[1]::]), d_931_tgtCond_, xs, pc)
                    if (d_932_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_927_v_)[0])
                    elif (d_932_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif default__.PreservesCond(d_932_w1_, d_930_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_927_v_)[1]::]), xs):
                        return MiscTypes.Option_Some((d_927_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_927_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_927_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in136_ = xs
                        in137_ = pc
                        in138_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_927_v_)[1]:len(seenOnPath):])
                        in139_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_927_v_)[1]:len(boolPath):])
                        xs = in136_
                        pc = in137_
                        seenOnPath = in138_
                        boolPath = in139_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def PreservesCond(c, seg, exits, xs):
        d_933_initState_ = State.default__.BuildInitState(c, 0)
        d_934_endState_ = default__.RunAll(seg, exits, xs, d_933_initState_)
        if (d_934_endState_).is_EState:
            return (d_934_endState_).Sat(c)
        elif True:
            return False

    @staticmethod
    def RunAll(seg, exits, xs, s):
        while True:
            with _dafny.label():
                if (len(seg)) == (0):
                    return s
                elif True:
                    source68_ = ((xs)[(seg)[0]]).Run(s, (exits)[0])
                    if source68_.is_EState:
                        d_935___mcc_h0_ = source68_.pc
                        d_936___mcc_h1_ = source68_.stack
                        d_937_st_ = d_936___mcc_h1_
                        d_938_p_ = d_935___mcc_h0_
                        in140_ = _dafny.SeqWithoutIsStrInference((seg)[1::])
                        in141_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                        in142_ = xs
                        in143_ = State.AState_EState(d_938_p_, d_937_st_)
                        seg = in140_
                        exits = in141_
                        xs = in142_
                        s = in143_
                        raise _dafny.TailCall()
                    elif True:
                        d_939___mcc_h2_ = source68_.msg
                        d_940_m_ = d_939___mcc_h2_
                        return State.AState_Error(d_940_m_)
                break

    @staticmethod
    def NodesToSeg(xn):
        d_941___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_941___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_941___accumulator_ = (d_941___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in144_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in144_
                    raise _dafny.TailCall()
                break

