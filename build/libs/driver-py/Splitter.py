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
            return LinSegments.LinSeg_JUMPSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        elif (((lastInst).op).opcode) == (87):
            return LinSegments.LinSeg_JUMPISeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        elif (((lastInst).op).opcode) == (243):
            return LinSegments.LinSeg_RETURNSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        elif (((lastInst).op).opcode) == (253):
            return LinSegments.LinSeg_STOPSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        elif (((lastInst).op).opcode) == (0):
            return LinSegments.LinSeg_STOPSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        elif (((lastInst).op).opcode) == (254):
            return LinSegments.LinSeg_INVALIDSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        elif True:
            return LinSegments.LinSeg_CONTSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))

    @staticmethod
    def SplitUpToTerminal(xs, curseq, collected):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    if (len(curseq)) == (0):
                        return collected
                    elif True:
                        d_727_newSeg_ = default__.BuildSeg(_dafny.SeqWithoutIsStrInference((curseq)[:(len(curseq)) - (1):]), (curseq)[(len(curseq)) - (1)])
                        return (collected) + (_dafny.SeqWithoutIsStrInference([d_727_newSeg_]))
                elif ((((xs)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    if (len(curseq)) == (0):
                        in63_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in64_ = _dafny.SeqWithoutIsStrInference([(xs)[0]])
                        in65_ = collected
                        xs = in63_
                        curseq = in64_
                        collected = in65_
                        raise _dafny.TailCall()
                    elif True:
                        d_728_newSeg_ = default__.BuildSeg(_dafny.SeqWithoutIsStrInference((curseq)[:(len(curseq)) - (1):]), (curseq)[(len(curseq)) - (1)])
                        in66_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in67_ = _dafny.SeqWithoutIsStrInference([(xs)[0]])
                        in68_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_728_newSeg_]))
                        xs = in66_
                        curseq = in67_
                        collected = in68_
                        raise _dafny.TailCall()
                elif ((xs)[0]).IsTerminal():
                    d_729_newSeg_ = default__.BuildSeg(curseq, (xs)[0])
                    in69_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in70_ = _dafny.SeqWithoutIsStrInference([])
                    in71_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_729_newSeg_]))
                    xs = in69_
                    curseq = in70_
                    collected = in71_
                    raise _dafny.TailCall()
                elif True:
                    in72_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in73_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in74_ = collected
                    xs = in72_
                    curseq = in73_
                    collected = in74_
                    raise _dafny.TailCall()
                break

