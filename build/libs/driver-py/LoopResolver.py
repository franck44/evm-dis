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
                    in129_ = xs
                    in130_ = pc
                    in131_ = s
                    in132_ = (index) + (1)
                    xs = in129_
                    pc = in130_
                    s = in131_
                    index = in132_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SafeLoopFound(xs, pc, seenOnPath, boolPath):
        while True:
            with _dafny.label():
                source64_ = default__.FindFirstNodeWithPC(xs, pc, seenOnPath, 0)
                if source64_.is_None:
                    return MiscTypes.Option_None()
                elif True:
                    d_778___mcc_h0_ = source64_.v
                    d_779_v_ = d_778___mcc_h0_
                    d_780_init_ = (seenOnPath)[(d_779_v_)[1]]
                    d_781_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_779_v_)[1]::])
                    d_782_segs_ = default__.NodesToSeg(d_781_path_)
                    d_783_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_784_w1_ = LinSegments.default__.WPreSeqSegs(d_782_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_779_v_)[1]::]), d_783_tgtCond_, xs, pc)
                    if (d_784_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_779_v_)[0])
                    elif (d_784_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif default__.PreservesCond(d_784_w1_, d_782_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_779_v_)[1]::]), xs):
                        return MiscTypes.Option_Some((d_779_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_779_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_779_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in133_ = xs
                        in134_ = pc
                        in135_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_779_v_)[1]:len(seenOnPath):])
                        in136_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_779_v_)[1]:len(boolPath):])
                        xs = in133_
                        pc = in134_
                        seenOnPath = in135_
                        boolPath = in136_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def PreservesCond(c, seg, exits, xs):
        d_785_initState_ = State.default__.BuildInitState(c, 0)
        d_786_endState_ = default__.RunAll(seg, exits, xs, d_785_initState_)
        if (d_786_endState_).is_EState:
            return (d_786_endState_).Sat(c)
        elif True:
            return False

    @staticmethod
    def RunAll(seg, exits, xs, s):
        while True:
            with _dafny.label():
                if (len(seg)) == (0):
                    return s
                elif True:
                    source65_ = ((xs)[(seg)[0]]).Run(s, (exits)[0])
                    if source65_.is_EState:
                        d_787___mcc_h0_ = source65_.pc
                        d_788___mcc_h1_ = source65_.stack
                        d_789_st_ = d_788___mcc_h1_
                        d_790_p_ = d_787___mcc_h0_
                        in137_ = _dafny.SeqWithoutIsStrInference((seg)[1::])
                        in138_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                        in139_ = xs
                        in140_ = State.AState_EState(d_790_p_, d_789_st_)
                        seg = in137_
                        exits = in138_
                        xs = in139_
                        s = in140_
                        raise _dafny.TailCall()
                    elif True:
                        d_791___mcc_h2_ = source65_.msg
                        d_792_m_ = d_791___mcc_h2_
                        return State.AState_Error(d_792_m_)
                break

    @staticmethod
    def NodesToSeg(xn):
        d_793___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_793___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_793___accumulator_ = (d_793___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in141_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in141_
                    raise _dafny.TailCall()
                break

