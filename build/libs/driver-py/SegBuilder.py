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
import Instructions
import BinaryDecoder
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
                    d_92_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source6_ = d_92_x_
                    if source6_.is_Left:
                        d_93___mcc_h0_ = source6_.l
                        d_94_v_ = d_93___mcc_h0_
                        return MiscTypes.Either_Left(d_94_v_)
                    elif True:
                        d_95___mcc_h1_ = source6_.r
                        d_96_v_ = d_95___mcc_h1_
                        in23_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in24_ = d_96_v_
                        xs = in23_
                        pos = in24_
                        raise _dafny.TailCall()
                break

