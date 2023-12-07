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
                    in134_ = xs
                    in135_ = pc
                    in136_ = s
                    in137_ = (index) + (1)
                    xs = in134_
                    pc = in135_
                    s = in136_
                    index = in137_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SafeLoopFound(xs, pc, seenOnPath, boolPath, jumpDests):
        while True:
            with _dafny.label():
                source68_ = default__.FindFirstNodeWithPC(xs, pc, seenOnPath, 0)
                if source68_.is_None:
                    return MiscTypes.Option_None()
                elif True:
                    d_962___mcc_h0_ = source68_.v
                    d_963_v_ = d_962___mcc_h0_
                    d_964_init_ = (seenOnPath)[(d_963_v_)[1]]
                    d_965_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_963_v_)[1]::])
                    d_966_segs_ = default__.NodesToSeg(d_965_path_)
                    d_967_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_968_w1_ = LinSegments.default__.WPreSeqSegs(d_966_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_963_v_)[1]::]), d_967_tgtCond_, xs, pc)
                    if (d_968_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_963_v_)[0])
                    elif (d_968_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif default__.PreservesCond(d_968_w1_, d_966_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_963_v_)[1]::]), xs, jumpDests):
                        return MiscTypes.Option_Some((d_963_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_963_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_963_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in138_ = xs
                        in139_ = pc
                        in140_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_963_v_)[1]:len(seenOnPath):])
                        in141_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_963_v_)[1]:len(boolPath):])
                        in142_ = jumpDests
                        xs = in138_
                        pc = in139_
                        seenOnPath = in140_
                        boolPath = in141_
                        jumpDests = in142_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def PreservesCond(c, seg, exits, xs, jumpDests):
        d_969_initState_ = State.default__.BuildInitState(c, 0)
        d_970_endState_ = default__.RunAll(seg, exits, xs, d_969_initState_, jumpDests)
        if (d_970_endState_).is_EState:
            return (d_970_endState_).Sat(c)
        elif True:
            return False

    @staticmethod
    def RunAll(seg, exits, xs, s, jumpDests):
        while True:
            with _dafny.label():
                if (len(seg)) == (0):
                    return s
                elif True:
                    source69_ = ((xs)[(seg)[0]]).Run(s, (exits)[0], jumpDests)
                    if source69_.is_EState:
                        d_971___mcc_h0_ = source69_.pc
                        d_972___mcc_h1_ = source69_.stack
                        d_973_st_ = d_972___mcc_h1_
                        d_974_p_ = d_971___mcc_h0_
                        in143_ = _dafny.SeqWithoutIsStrInference((seg)[1::])
                        in144_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                        in145_ = xs
                        in146_ = State.AState_EState(d_974_p_, d_973_st_)
                        in147_ = jumpDests
                        seg = in143_
                        exits = in144_
                        xs = in145_
                        s = in146_
                        jumpDests = in147_
                        raise _dafny.TailCall()
                    elif True:
                        d_975___mcc_h2_ = source69_.msg
                        d_976_m_ = d_975___mcc_h2_
                        return State.AState_Error(d_976_m_)
                break

    @staticmethod
    def NodesToSeg(xn):
        d_977___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_977___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_977___accumulator_ = (d_977___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in148_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in148_
                    raise _dafny.TailCall()
                break

