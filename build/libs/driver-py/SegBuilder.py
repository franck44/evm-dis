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
                    d_740_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source48_ = d_740_x_
                    if source48_.is_Left:
                        d_741___mcc_h0_ = source48_.l
                        d_742_v_ = d_741___mcc_h0_
                        return MiscTypes.Either_Left(d_742_v_)
                    elif True:
                        d_743___mcc_h1_ = source48_.r
                        d_744_v_ = d_743___mcc_h1_
                        in71_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in72_ = d_744_v_
                        xs = in71_
                        pos = in72_
                        raise _dafny.TailCall()
                break

