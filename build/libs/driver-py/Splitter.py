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

# Module: Splitter

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildSeg(xs, lastInst):
        if (((lastInst).op).opcode) == (86):
            return LinSegments.LinSeg_JUMPSeg(xs, lastInst, default__.DeltaOperandsHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst])), 0))
        elif (((lastInst).op).opcode) == (87):
            return LinSegments.LinSeg_JUMPISeg(xs, lastInst, default__.DeltaOperandsHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst])), 0))
        elif (((lastInst).op).opcode) == (243):
            return LinSegments.LinSeg_RETURNSeg(xs, lastInst, default__.DeltaOperandsHelper(xs, 0))
        elif (((lastInst).op).opcode) == (253):
            return LinSegments.LinSeg_STOPSeg(xs, lastInst, default__.DeltaOperandsHelper(xs, 0))
        elif (((lastInst).op).opcode) == (0):
            return LinSegments.LinSeg_STOPSeg(xs, lastInst, default__.DeltaOperandsHelper(xs, 0))
        elif (((lastInst).op).opcode) == (254):
            return LinSegments.LinSeg_INVALIDSeg(xs, lastInst, default__.DeltaOperandsHelper(xs, 0))
        elif True:
            return LinSegments.LinSeg_CONTSeg(xs, lastInst, default__.DeltaOperandsHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst])), 0))

    @staticmethod
    def EndOfSegment(xs):
        if ((xs)[0]).IsTerminal():
            return True
        elif ((len(xs)) > (1)) and (((xs)[1]).IsJumpDest()):
            return True
        elif True:
            return False

    @staticmethod
    def SplitUpToTerminal(xs, curseq, collected):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return collected
                elif (len(xs)) == (1):
                    return (collected) + (_dafny.SeqWithoutIsStrInference([default__.BuildSeg(curseq, (xs)[0])]))
                elif default__.EndOfSegment(xs):
                    d_555_newSeg_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in55_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in56_ = _dafny.SeqWithoutIsStrInference([])
                    in57_ = (collected) + (_dafny.SeqWithoutIsStrInference([default__.BuildSeg(curseq, (xs)[0])]))
                    xs = in55_
                    curseq = in56_
                    collected = in57_
                    raise _dafny.TailCall()
                elif True:
                    in58_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in59_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in60_ = collected
                    xs = in58_
                    curseq = in59_
                    collected = in60_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DeltaOperandsHelper(xs, current):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return current
                elif True:
                    d_556_e_ = (current) + (((((xs)[0]).op).pushes) - ((((xs)[0]).op).pops))
                    in61_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in62_ = d_556_e_
                    xs = in61_
                    current = in62_
                    raise _dafny.TailCall()
                break

