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
                    in123_ = xs
                    in124_ = pc
                    in125_ = s
                    in126_ = (index) + (1)
                    xs = in123_
                    pc = in124_
                    s = in125_
                    index = in126_
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
                    d_770___mcc_h0_ = source64_.v
                    d_771_v_ = d_770___mcc_h0_
                    d_772_init_ = (seenOnPath)[(d_771_v_)[1]]
                    d_773_path_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_771_v_)[1]::])
                    d_774_segs_ = default__.NodesToSeg(d_773_path_)
                    d_775_tgtCond_ = ((xs)[(((seenOnPath)[(len(seenOnPath)) - (1)]).seg).v]).LeadsTo(pc, (boolPath)[(len(boolPath)) - (1)])
                    d_776_w1_ = LinSegments.default__.WPreSeqSegs(d_774_segs_, _dafny.SeqWithoutIsStrInference((boolPath)[(d_771_v_)[1]::]), d_775_tgtCond_, xs, pc)
                    if (d_776_w1_).is_StTrue:
                        return MiscTypes.Option_Some((d_771_v_)[0])
                    elif ((0) < (len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_771_v_)[1]:len(seenOnPath):])))) and ((len(_dafny.SeqWithoutIsStrInference((seenOnPath)[(d_771_v_)[1]:len(seenOnPath):]))) < (len(seenOnPath))):
                        in127_ = xs
                        in128_ = pc
                        in129_ = _dafny.SeqWithoutIsStrInference((seenOnPath)[(d_771_v_)[1]:len(seenOnPath):])
                        in130_ = _dafny.SeqWithoutIsStrInference((boolPath)[(d_771_v_)[1]:len(boolPath):])
                        xs = in127_
                        pc = in128_
                        seenOnPath = in129_
                        boolPath = in130_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    @staticmethod
    def NodesToSeg(xn):
        d_777___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xn)) == (0):
                    return (d_777___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_777___accumulator_ = (d_777___accumulator_) + (_dafny.SeqWithoutIsStrInference([(((xn)[0]).seg).v]))
                    in131_ = _dafny.SeqWithoutIsStrInference((xn)[1::])
                    xn = in131_
                    raise _dafny.TailCall()
                break

