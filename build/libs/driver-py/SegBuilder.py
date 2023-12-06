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
                    d_716_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source48_ = d_716_x_
                    if source48_.is_Left:
                        d_717___mcc_h0_ = source48_.l
                        d_718_v_ = d_717___mcc_h0_
                        return MiscTypes.Either_Left(d_718_v_)
                    elif True:
                        d_719___mcc_h1_ = source48_.r
                        d_720_v_ = d_719___mcc_h1_
                        in70_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in71_ = d_720_v_
                        xs = in70_
                        pos = in71_
                        raise _dafny.TailCall()
                break

