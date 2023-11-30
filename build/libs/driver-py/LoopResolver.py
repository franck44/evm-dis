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
                source65_ = default__.FindFirstNodeWithPC(xs, pc, seenOnPath, 0)
                if source65_.is_None:
                    return MiscTypes.Option_None()
                elif True:
                    d_915___mcc_h0_ = source65_.v
                    d_916_v_ = d_915___mcc_h0_
                    d_917_init_ = (seenOnPath)[(d_916_v_)[1]]
                    d_918_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_916_v_)[1]::])
                    d_919_segs_ = default__.NodesToSeg(d_918_path_)
                    d_920_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_921_w1_ = LinSegments.default__.WPreSeqSegs(d_919_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_916_v_)[1]::]), d_920_tgtCond_, xs, pc)
                    if (d_921_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_916_v_)[0])
                    elif (d_921_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif default__.PreservesCond(d_921_w1_, d_919_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_916_v_)[1]::]), xs):
                        return MiscTypes.Option_Some((d_916_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_916_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_916_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in136_ = xs
                        in137_ = pc
                        in138_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_916_v_)[1]:len(seenOnPath):])
                        in139_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_916_v_)[1]:len(boolPath):])
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
        d_922_initState_ = State.default__.BuildInitState(c, 0)
        d_923_endState_ = default__.RunAll(seg, exits, xs, d_922_initState_)
        if (d_923_endState_).is_EState:
            return (d_923_endState_).Sat(c)
        elif True:
            return False

    @staticmethod
    def RunAll(seg, exits, xs, s):
        while True:
            with _dafny.label():
                if (len(seg)) == (0):
                    return s
                elif True:
                    source66_ = ((xs)[(seg)[0]]).Run(s, (exits)[0])
                    if source66_.is_EState:
                        d_924___mcc_h0_ = source66_.pc
                        d_925___mcc_h1_ = source66_.stack
                        d_926_st_ = d_925___mcc_h1_
                        d_927_p_ = d_924___mcc_h0_
                        in140_ = _dafny.SeqWithoutIsStrInference((seg)[1::])
                        in141_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                        in142_ = xs
                        in143_ = State.AState_EState(d_927_p_, d_926_st_)
                        seg = in140_
                        exits = in141_
                        xs = in142_
                        s = in143_
                        raise _dafny.TailCall()
                    elif True:
                        d_928___mcc_h2_ = source66_.msg
                        d_929_m_ = d_928___mcc_h2_
                        return State.AState_Error(d_929_m_)
                break

    @staticmethod
    def NodesToSeg(xn):
        d_930___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_930___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_930___accumulator_ = (d_930___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in144_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in144_
                    raise _dafny.TailCall()
                break

