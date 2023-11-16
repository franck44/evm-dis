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
                    d_511_newSeg_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in43_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in44_ = _dafny.SeqWithoutIsStrInference([])
                    in45_ = (collected) + (_dafny.SeqWithoutIsStrInference([default__.BuildSeg(curseq, (xs)[0])]))
                    xs = in43_
                    curseq = in44_
                    collected = in45_
                    raise _dafny.TailCall()
                elif True:
                    in46_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in47_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in48_ = collected
                    xs = in46_
                    curseq = in47_
                    collected = in48_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DeltaOperandsHelper(xs, current):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return current
                elif True:
                    d_512_e_ = (current) + (((((xs)[0]).op).pushes) - ((((xs)[0]).op).pops))
                    in49_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in50_ = d_512_e_
                    xs = in49_
                    current = in50_
                    raise _dafny.TailCall()
                break

