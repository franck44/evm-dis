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
                    in135_ = xs
                    in136_ = pc
                    in137_ = s
                    in138_ = (index) + (1)
                    xs = in135_
                    pc = in136_
                    s = in137_
                    index = in138_
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
                    d_963___mcc_h0_ = source69_.v
                    d_964_v_ = d_963___mcc_h0_
                    d_965_init_ = (seenOnPath)[(d_964_v_)[1]]
                    d_966_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_964_v_)[1]::])
                    d_967_segs_ = default__.NodesToSeg(d_966_path_)
                    d_968_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_969_w1_ = LinSegments.default__.WPreSeqSegs(d_967_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_964_v_)[1]::]), d_968_tgtCond_, xs, pc)
                    if (d_969_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_964_v_)[0])
                    elif (d_969_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif default__.PreservesCond(d_969_w1_, d_967_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_964_v_)[1]::]), xs, jumpDests):
                        return MiscTypes.Option_Some((d_964_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_964_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_964_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in139_ = xs
                        in140_ = pc
                        in141_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_964_v_)[1]:len(seenOnPath):])
                        in142_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_964_v_)[1]:len(boolPath):])
                        in143_ = jumpDests
                        xs = in139_
                        pc = in140_
                        seenOnPath = in141_
                        boolPath = in142_
                        jumpDests = in143_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def PreservesCond(c, seg, exits, xs, jumpDests):
        d_970_initState_ = State.default__.BuildInitState(c, 0)
        d_971_endState_ = default__.RunAll(seg, exits, xs, d_970_initState_, jumpDests)
        if (d_971_endState_).is_EState:
            return (d_971_endState_).Sat(c)
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
                        d_972___mcc_h0_ = source70_.pc
                        d_973___mcc_h1_ = source70_.stack
                        d_974_st_ = d_973___mcc_h1_
                        d_975_p_ = d_972___mcc_h0_
                        in144_ = _dafny.SeqWithoutIsStrInference((seg)[1::])
                        in145_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                        in146_ = xs
                        in147_ = State.AState_EState(d_975_p_, d_974_st_)
                        in148_ = jumpDests
                        seg = in144_
                        exits = in145_
                        xs = in146_
                        s = in147_
                        jumpDests = in148_
                        raise _dafny.TailCall()
                    elif True:
                        d_976___mcc_h2_ = source70_.msg
                        d_977_m_ = d_976___mcc_h2_
                        return State.AState_Error(d_977_m_)
                break

    @staticmethod
    def NodesToSeg(xn):
        d_978___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_978___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_978___accumulator_ = (d_978___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in149_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in149_
                    raise _dafny.TailCall()
                break

