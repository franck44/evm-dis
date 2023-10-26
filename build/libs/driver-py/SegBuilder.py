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
                    d_178_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source7_ = d_178_x_
                    if source7_.is_Left:
                        d_179___mcc_h0_ = source7_.l
                        d_180_v_ = d_179___mcc_h0_
                        return MiscTypes.Either_Left(d_180_v_)
                    elif True:
                        d_181___mcc_h1_ = source7_.r
                        d_182_v_ = d_181___mcc_h1_
                        in28_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in29_ = d_182_v_
                        xs = in28_
                        pos = in29_
                        raise _dafny.TailCall()
                break

