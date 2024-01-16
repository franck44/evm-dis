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
                    d_754_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source49_ = d_754_x_
                    if source49_.is_Left:
                        d_755___mcc_h0_ = source49_.l
                        d_756_v_ = d_755___mcc_h0_
                        return MiscTypes.Either_Left(d_756_v_)
                    elif True:
                        d_757___mcc_h1_ = source49_.r
                        d_758_v_ = d_757___mcc_h1_
                        in89_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in90_ = d_758_v_
                        xs = in89_
                        pos = in90_
                        raise _dafny.TailCall()
                break

