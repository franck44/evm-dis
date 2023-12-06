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
                    in133_ = xs
                    in134_ = pc
                    in135_ = s
                    in136_ = (index) + (1)
                    xs = in133_
                    pc = in134_
                    s = in135_
                    index = in136_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SafeLoopFound(xs, pc, seenOnPath, boolPath):
        while True:
            with _dafny.label():
                source69_ = default__.FindFirstNodeWithPC(xs, pc, seenOnPath, 0)
                if source69_.is_None:
                    return MiscTypes.Option_None()
                elif True:
                    d_961___mcc_h0_ = source69_.v
                    d_962_v_ = d_961___mcc_h0_
                    d_963_init_ = (seenOnPath)[(d_962_v_)[1]]
                    d_964_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_962_v_)[1]::])
                    d_965_segs_ = default__.NodesToSeg(d_964_path_)
                    d_966_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_967_w1_ = LinSegments.default__.WPreSeqSegs(d_965_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_962_v_)[1]::]), d_966_tgtCond_, xs, pc)
                    if (d_967_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_962_v_)[0])
                    elif (d_967_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif default__.PreservesCond(d_967_w1_, d_965_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_962_v_)[1]::]), xs):
                        return MiscTypes.Option_Some((d_962_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_962_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_962_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in137_ = xs
                        in138_ = pc
                        in139_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_962_v_)[1]:len(seenOnPath):])
                        in140_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_962_v_)[1]:len(boolPath):])
                        xs = in137_
                        pc = in138_
                        seenOnPath = in139_
                        boolPath = in140_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def PreservesCond(c, seg, exits, xs):
        d_968_initState_ = State.default__.BuildInitState(c, 0)
        d_969_endState_ = default__.RunAll(seg, exits, xs, d_968_initState_)
        if (d_969_endState_).is_EState:
            return (d_969_endState_).Sat(c)
        elif True:
            return False

    @staticmethod
    def RunAll(seg, exits, xs, s):
        while True:
            with _dafny.label():
                if (len(seg)) == (0):
                    return s
                elif True:
                    source70_ = ((xs)[(seg)[0]]).Run(s, (exits)[0])
                    if source70_.is_EState:
                        d_970___mcc_h0_ = source70_.pc
                        d_971___mcc_h1_ = source70_.stack
                        d_972_st_ = d_971___mcc_h1_
                        d_973_p_ = d_970___mcc_h0_
                        in141_ = _dafny.SeqWithoutIsStrInference((seg)[1::])
                        in142_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                        in143_ = xs
                        in144_ = State.AState_EState(d_973_p_, d_972_st_)
                        seg = in141_
                        exits = in142_
                        xs = in143_
                        s = in144_
                        raise _dafny.TailCall()
                    elif True:
                        d_974___mcc_h2_ = source70_.msg
                        d_975_m_ = d_974___mcc_h2_
                        return State.AState_Error(d_975_m_)
                break

    @staticmethod
    def NodesToSeg(xn):
        d_976___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_976___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_976___accumulator_ = (d_976___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in145_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in145_
                    raise _dafny.TailCall()
                break

