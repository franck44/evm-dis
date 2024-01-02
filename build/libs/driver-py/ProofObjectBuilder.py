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
import CFGState
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
        d_1013___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv9_ = xs
                if (len(xs)) == (0):
                    return (d_1013___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_1014_wpOp_ = ((xs)[0]).WeakestPreOperands(0)
                    d_1015_wpCap_ = ((xs)[0]).WeakestPreCapacity(0)
                    def iife36_(_pat_let17_0):
                        def iife37_(d_1017_tgt_):
                            return ProofObject.ProofObj_JUMP((pat_let_tv9_)[0], d_1014_wpOp_, d_1015_wpCap_, d_1017_tgt_, _dafny.Map({}))
                        return iife37_(_pat_let17_0)
                    d_1016_obj_ = (iife36_(SegBuilder.default__.JUMPResolver((xs)[0])) if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg) else (ProofObject.ProofObj_CONT((xs)[0], d_1014_wpOp_, d_1015_wpCap_, _dafny.Map({})) if ((xs)[0]).is_CONTSeg else ProofObject.ProofObj_TERMINAL((xs)[0], d_1014_wpOp_, d_1015_wpCap_, _dafny.Map({}))))
                    d_1013___accumulator_ = (d_1013___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_1016_obj_]))
                    in135_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in135_
                    raise _dafny.TailCall()
                break

