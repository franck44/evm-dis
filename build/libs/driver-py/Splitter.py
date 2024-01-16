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
    def SplitUpToTerminal(xs, maxSegSize, curseq, collected):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    if (len(curseq)) == (0):
                        return collected
                    elif True:
                        d_750_newSeg_ = default__.BuildSeg(_dafny.SeqWithoutIsStrInference((curseq)[:(len(curseq)) - (1):]), (curseq)[(len(curseq)) - (1)])
                        return (collected) + (_dafny.SeqWithoutIsStrInference([d_750_newSeg_]))
                elif ((((xs)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    if (len(curseq)) == (0):
                        in69_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in70_ = maxSegSize
                        in71_ = _dafny.SeqWithoutIsStrInference([(xs)[0]])
                        in72_ = collected
                        xs = in69_
                        maxSegSize = in70_
                        curseq = in71_
                        collected = in72_
                        raise _dafny.TailCall()
                    elif True:
                        d_751_newSeg_ = default__.BuildSeg(_dafny.SeqWithoutIsStrInference((curseq)[:(len(curseq)) - (1):]), (curseq)[(len(curseq)) - (1)])
                        in73_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in74_ = maxSegSize
                        in75_ = _dafny.SeqWithoutIsStrInference([(xs)[0]])
                        in76_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_751_newSeg_]))
                        xs = in73_
                        maxSegSize = in74_
                        curseq = in75_
                        collected = in76_
                        raise _dafny.TailCall()
                elif ((xs)[0]).IsTerminal():
                    d_752_newSeg_ = default__.BuildSeg(curseq, (xs)[0])
                    in77_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in78_ = maxSegSize
                    in79_ = _dafny.SeqWithoutIsStrInference([])
                    in80_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_752_newSeg_]))
                    xs = in77_
                    maxSegSize = in78_
                    curseq = in79_
                    collected = in80_
                    raise _dafny.TailCall()
                elif ((maxSegSize).is_Some) and ((len(curseq)) >= ((maxSegSize).v)):
                    d_753_newSeg_ = default__.BuildSeg(curseq, (xs)[0])
                    in81_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in82_ = maxSegSize
                    in83_ = _dafny.SeqWithoutIsStrInference([])
                    in84_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_753_newSeg_]))
                    xs = in81_
                    maxSegSize = in82_
                    curseq = in83_
                    collected = in84_
                    raise _dafny.TailCall()
                elif True:
                    in85_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in86_ = maxSegSize
                    in87_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in88_ = collected
                    xs = in85_
                    maxSegSize = in86_
                    curseq = in87_
                    collected = in88_
                    raise _dafny.TailCall()
                break

