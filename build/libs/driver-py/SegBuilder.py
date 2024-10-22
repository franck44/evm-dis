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
import Splitter as Splitter

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
                    d_0_x_ = ((xs)[(len(xs)) - (1)]).StackPosBackWardTracker(pos)
                    source0_ = d_0_x_
                    if True:
                        if source0_.is_Left:
                            d_1_v_ = source0_.l
                            return MiscTypes.Either_Left(d_1_v_)
                    if True:
                        d_2_v_ = source0_.r
                        in0_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                        in1_ = d_2_v_
                        xs = in0_
                        pos = in1_
                        raise _dafny.TailCall()
                break

