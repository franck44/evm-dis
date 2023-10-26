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
            return LinSegments.LinSeg_JUMPSeg(xs, lastInst)
        elif (((lastInst).op).opcode) == (87):
            return LinSegments.LinSeg_JUMPISeg(xs, lastInst)
        elif (((lastInst).op).opcode) == (243):
            return LinSegments.LinSeg_RETURNSeg(xs, lastInst)
        elif (((lastInst).op).opcode) == (0):
            return LinSegments.LinSeg_STOPSeg(xs, lastInst)
        elif True:
            return LinSegments.LinSeg_UNKNOWNSeg(xs, lastInst)

    @staticmethod
    def SplitUpToTerminal(xs, curseq, collected):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return collected
                elif (len(xs)) == (1):
                    return (collected) + (_dafny.SeqWithoutIsStrInference([default__.BuildSeg(curseq, (xs)[0])]))
                elif ((xs)[0]).IsTerminal():
                    d_177_newSeg_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in22_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in23_ = _dafny.SeqWithoutIsStrInference([])
                    in24_ = (collected) + (_dafny.SeqWithoutIsStrInference([default__.BuildSeg(curseq, (xs)[0])]))
                    xs = in22_
                    curseq = in23_
                    collected = in24_
                    raise _dafny.TailCall()
                elif True:
                    in25_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in26_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in27_ = collected
                    xs = in25_
                    curseq = in26_
                    collected = in27_
                    raise _dafny.TailCall()
                break

