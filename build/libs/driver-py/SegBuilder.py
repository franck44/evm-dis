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
                    d_501_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source39_ = d_501_x_
                    if source39_.is_Left:
                        d_502___mcc_h0_ = source39_.l
                        d_503_v_ = d_502___mcc_h0_
                        return MiscTypes.Either_Left(d_503_v_)
                    elif True:
                        d_504___mcc_h1_ = source39_.r
                        d_505_v_ = d_504___mcc_h1_
                        in47_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in48_ = d_505_v_
                        xs = in47_
                        pos = in48_
                        raise _dafny.TailCall()
                break

