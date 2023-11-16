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
                    d_513_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source41_ = d_513_x_
                    if source41_.is_Left:
                        d_514___mcc_h0_ = source41_.l
                        d_515_v_ = d_514___mcc_h0_
                        return MiscTypes.Either_Left(d_515_v_)
                    elif True:
                        d_516___mcc_h1_ = source41_.r
                        d_517_v_ = d_516___mcc_h1_
                        in51_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in52_ = d_517_v_
                        xs = in51_
                        pos = in52_
                        raise _dafny.TailCall()
                break

