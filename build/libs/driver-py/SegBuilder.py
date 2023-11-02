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
                    d_189_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source8_ = d_189_x_
                    if source8_.is_Left:
                        d_190___mcc_h0_ = source8_.l
                        d_191_v_ = d_190___mcc_h0_
                        return MiscTypes.Either_Left(d_191_v_)
                    elif True:
                        d_192___mcc_h1_ = source8_.r
                        d_193_v_ = d_192___mcc_h1_
                        in31_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in32_ = d_193_v_
                        xs = in31_
                        pos = in32_
                        raise _dafny.TailCall()
                break

