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

# Module: ProofObjectBuilder

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildProofObject(xs):
        d_782___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv0_ = xs
                if (len(xs)) == (0):
                    return (d_782___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_783_wpOp_ = ((xs)[0]).WeakestPreOperands(0)
                    d_784_wpCap_ = ((xs)[0]).WeakestPreCapacity(0)
                    def iife0_(_pat_let0_0):
                        def iife1_(d_786_tgt_):
                            return ProofObject.ProofObj_JUMP((pat_let_tv0_)[0], d_783_wpOp_, d_784_wpCap_, d_786_tgt_, _dafny.Map({}))
                        return iife1_(_pat_let0_0)
                    d_785_obj_ = (iife0_(SegBuilder.default__.JUMPResolver((xs)[0])) if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg) else (ProofObject.ProofObj_CONT((xs)[0], d_783_wpOp_, d_784_wpCap_, _dafny.Map({})) if ((xs)[0]).is_CONTSeg else ProofObject.ProofObj_TERMINAL((xs)[0], d_783_wpOp_, d_784_wpCap_, _dafny.Map({}))))
                    d_782___accumulator_ = (d_782___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_785_obj_]))
                    in81_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in81_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDests(xs):
        d_787___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_787___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_787___accumulator_ = (d_787___accumulator_) + (((xs)[0]).CollectJumpDest(((xs)[0]).Ins()))
                    in82_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in82_
                    raise _dafny.TailCall()
                break

