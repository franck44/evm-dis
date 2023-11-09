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
        elif (((lastInst).op).opcode) == (0):
            return LinSegments.LinSeg_STOPSeg(xs, lastInst, default__.DeltaOperandsHelper(xs, 0))
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
                    d_499_newSeg_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in39_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in40_ = _dafny.SeqWithoutIsStrInference([])
                    in41_ = (collected) + (_dafny.SeqWithoutIsStrInference([default__.BuildSeg(curseq, (xs)[0])]))
                    xs = in39_
                    curseq = in40_
                    collected = in41_
                    raise _dafny.TailCall()
                elif True:
                    in42_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in43_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in44_ = collected
                    xs = in42_
                    curseq = in43_
                    collected = in44_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DeltaOperandsHelper(xs, current):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return current
                elif True:
                    d_500_e_ = (current) + (((((xs)[0]).op).pushes) - ((((xs)[0]).op).pops))
                    in45_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in46_ = d_500_e_
                    xs = in45_
                    current = in46_
                    raise _dafny.TailCall()
                break

