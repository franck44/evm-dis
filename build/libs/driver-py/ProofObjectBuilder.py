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
import CFGState
import ProofObject
import PrettyIns
import PrettyPrinters
import Automata
import SeqOfSets
import PartitionMod
import GStateMinimiser
import Statistics
import HTML
import EVMObject
import ArgParser

# Module: ProofObjectBuilder

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildProofObject(xs):
        d_1053___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv17_ = xs
                if (len(xs)) == (0):
                    return (d_1053___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_1054_wpOp_ = ((xs)[0]).WeakestPreOperands(((xs)[0]).Ins(), 0)
                    d_1055_wpCap_ = ((xs)[0]).WeakestPreCapacity(0)
                    def iife39_(_pat_let18_0):
                        def iife40_(d_1057_tgt_):
                            return ProofObject.ProofObj_JUMP((pat_let_tv17_)[0], d_1054_wpOp_, d_1055_wpCap_, d_1057_tgt_, _dafny.Map({}))
                        return iife40_(_pat_let18_0)
                    d_1056_obj_ = (iife39_(SegBuilder.default__.JUMPResolver((xs)[0])) if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg) else (ProofObject.ProofObj_CONT((xs)[0], d_1054_wpOp_, d_1055_wpCap_, _dafny.Map({})) if ((xs)[0]).is_CONTSeg else ProofObject.ProofObj_TERMINAL((xs)[0], d_1054_wpOp_, d_1055_wpCap_, _dafny.Map({}))))
                    d_1053___accumulator_ = (d_1053___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_1056_obj_]))
                    in167_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in167_
                    raise _dafny.TailCall()
                break

