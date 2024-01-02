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

# Module: SegBuilder

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def JUMPResolver(s):
        return default__.StackPositionTracker((s).ins, 0)

    @staticmethod
    def StackPositionTracker(xs, pos):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return MiscTypes.Either_Right(pos)
                elif True:
                    d_730_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source47_ = d_730_x_
                    if source47_.is_Left:
                        d_731___mcc_h0_ = source47_.l
                        d_732_v_ = d_731___mcc_h0_
                        return MiscTypes.Either_Left(d_732_v_)
                    elif True:
                        d_733___mcc_h1_ = source47_.r
                        d_734_v_ = d_733___mcc_h1_
                        in72_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in73_ = d_734_v_
                        xs = in72_
                        pos = in73_
                        raise _dafny.TailCall()
                break

