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
import EVMObject
import ArgParser
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph
import LoopResolver
import BuildCFGraphV2

# Module: ProofObjectBuilder

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildProofObject(xs):
        d_1046___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv61_ = xs
                if (len(xs)) == (0):
                    return (d_1046___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_1047_wpOp_ = ((xs)[0]).WeakestPreOperands(0)
                    d_1048_wpCap_ = ((xs)[0]).WeakestPreCapacity(0)
                    def iife83_(_pat_let41_0):
                        def iife84_(d_1050_tgt_):
                            return ProofObject.ProofObj_JUMP((pat_let_tv61_)[0], d_1047_wpOp_, d_1048_wpCap_, d_1050_tgt_, _dafny.Map({}))
                        return iife84_(_pat_let41_0)
                    d_1049_obj_ = (iife83_(SegBuilder.default__.JUMPResolver((xs)[0])) if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg) else (ProofObject.ProofObj_CONT((xs)[0], d_1047_wpOp_, d_1048_wpCap_, _dafny.Map({})) if ((xs)[0]).is_CONTSeg else ProofObject.ProofObj_TERMINAL((xs)[0], d_1047_wpOp_, d_1048_wpCap_, _dafny.Map({}))))
                    d_1046___accumulator_ = (d_1046___accumulator_) + (_dafny.SeqWithoutIsStrInference([d_1049_obj_]))
                    in159_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in159_
                    raise _dafny.TailCall()
                break

