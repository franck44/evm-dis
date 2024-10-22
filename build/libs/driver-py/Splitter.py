import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import MiscTypes as MiscTypes
import Int as Int
import EVMConstants as EVMConstants
import EVMOpcodes as EVMOpcodes
import OpcodeDecoder as OpcodeDecoder
import Hex as Hex
import StackElement as StackElement
import WeakPre as WeakPre
import State as State
import EVMToolTips as EVMToolTips
import Instructions as Instructions
import BinaryDecoder as BinaryDecoder
import LinSegments as LinSegments

# Module: Splitter

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildSeg(xs, lastInst):
        source0_ = ((lastInst).op).opcode
        if True:
            if (source0_) == (86):
                return LinSegments.LinSeg_JUMPSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        if True:
            if (source0_) == (87):
                return LinSegments.LinSeg_JUMPISeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        if True:
            if (source0_) == (243):
                return LinSegments.LinSeg_RETURNSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        if True:
            if (source0_) == (253):
                return LinSegments.LinSeg_STOPSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        if True:
            if (source0_) == (0):
                return LinSegments.LinSeg_STOPSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        if True:
            if (source0_) == (254):
                return LinSegments.LinSeg_INVALIDSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))
        if True:
            return LinSegments.LinSeg_CONTSeg(xs, lastInst, LinSegments.default__.StackEffectHelper((xs) + (_dafny.SeqWithoutIsStrInference([lastInst]))))

    @staticmethod
    def SplitUpToTerminal(xs, maxSegSize, curseq, collected):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    if (len(curseq)) == (0):
                        return collected
                    elif True:
                        d_0_newSeg_ = default__.BuildSeg(_dafny.SeqWithoutIsStrInference((curseq)[:(len(curseq)) - (1):]), (curseq)[(len(curseq)) - (1)])
                        return (collected) + (_dafny.SeqWithoutIsStrInference([d_0_newSeg_]))
                elif ((((xs)[0]).op).opcode) == (EVMConstants.default__.JUMPDEST):
                    if (len(curseq)) == (0):
                        in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in1_ = maxSegSize
                        in2_ = _dafny.SeqWithoutIsStrInference([(xs)[0]])
                        in3_ = collected
                        xs = in0_
                        maxSegSize = in1_
                        curseq = in2_
                        collected = in3_
                        raise _dafny.TailCall()
                    elif True:
                        d_1_newSeg_ = default__.BuildSeg(_dafny.SeqWithoutIsStrInference((curseq)[:(len(curseq)) - (1):]), (curseq)[(len(curseq)) - (1)])
                        in4_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                        in5_ = maxSegSize
                        in6_ = _dafny.SeqWithoutIsStrInference([(xs)[0]])
                        in7_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_1_newSeg_]))
                        xs = in4_
                        maxSegSize = in5_
                        curseq = in6_
                        collected = in7_
                        raise _dafny.TailCall()
                elif ((xs)[0]).IsTerminal():
                    d_2_newSeg_ = default__.BuildSeg(curseq, (xs)[0])
                    in8_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in9_ = maxSegSize
                    in10_ = _dafny.SeqWithoutIsStrInference([])
                    in11_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_2_newSeg_]))
                    xs = in8_
                    maxSegSize = in9_
                    curseq = in10_
                    collected = in11_
                    raise _dafny.TailCall()
                elif ((maxSegSize).is_Some) and ((len(curseq)) >= ((maxSegSize).v)):
                    d_3_newSeg_ = default__.BuildSeg(curseq, (xs)[0])
                    in12_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in13_ = maxSegSize
                    in14_ = _dafny.SeqWithoutIsStrInference([])
                    in15_ = (collected) + (_dafny.SeqWithoutIsStrInference([d_3_newSeg_]))
                    xs = in12_
                    maxSegSize = in13_
                    curseq = in14_
                    collected = in15_
                    raise _dafny.TailCall()
                elif True:
                    in16_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in17_ = maxSegSize
                    in18_ = (curseq) + (_dafny.SeqWithoutIsStrInference([(xs)[0]]))
                    in19_ = collected
                    xs = in16_
                    maxSegSize = in17_
                    curseq = in18_
                    collected = in19_
                    raise _dafny.TailCall()
                break

