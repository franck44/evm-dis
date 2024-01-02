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
    def SplitUpToTerminal(xs, curseq, collected):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    if (len(curseq)) == (0):
                        return collected
                    elif True:
                        d_726_newSeg_ = default__.BuildSeg(_dafny.SeqWithoutIsStrInference((curseq)[:(len(curseq)) - (1):]), (curseq)[(len(curseq)) - (1)])
                        return (collected) + (_dafny.SeqWithoutIsStrInference([d_726_newSeg_]))
                elif ((((xs)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    if (len(curseq)) == (0):
                        in58_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in59_ = _dafny.SeqWithoutIsStrInference([(xs)[0]])
                        in60_ = collected
                        xs = in58_
                        curseq = in59_
                        collected = in60_
                        raise _dafny.TailCall()
                    elif True:
                        d_727_newSeg_ = default__.BuildSeg(_dafny.SeqWithoutIsStrInference((curseq)[:(len(curseq)) - (1):]), (curseq)[(len(curseq)) - (1)])
                        in61_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in62_ = _dafny.SeqWithoutIsStrInference([(xs)[0]])
                        in63_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_727_newSeg_]))
                        xs = in61_
                        curseq = in62_
                        collected = in63_
                        raise _dafny.TailCall()
                elif ((xs)[0]).IsTerminal():
                    d_728_newSeg_ = default__.BuildSeg(curseq, (xs)[0])
                    in64_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in65_ = _dafny.SeqWithoutIsStrInference([])
                    in66_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_728_newSeg_]))
                    xs = in64_
                    curseq = in65_
                    collected = in66_
                    raise _dafny.TailCall()
                elif True:
                    in67_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in68_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in69_ = collected
                    xs = in67_
                    curseq = in68_
                    collected = in69_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DeltaOperandsHelper(xs, current):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return current
                elif True:
                    d_729_e_ = (current) + (((((xs)[0]).op).pushes) - ((((xs)[0]).op).pops))
                    in70_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in71_ = d_729_e_
                    xs = in70_
                    current = in71_
                    raise _dafny.TailCall()
                break

