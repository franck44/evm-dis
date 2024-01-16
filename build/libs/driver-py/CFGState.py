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
import SegBuilder

# Module: CFGState

class default__:
    def  __init__(self):
        pass

    @_dafny.classproperty
    def DEFAULT__GSTATE(instance):
        return GState_EGState(0, _dafny.SeqWithoutIsStrInference([]))

class GState:
    @classmethod
    def default(cls, ):
        return lambda: GState_EGState(int(0), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_EGState(self) -> bool:
        return isinstance(self, GState_EGState)
    @property
    def is_ErrorGState(self) -> bool:
        return isinstance(self, GState_ErrorGState)
    def ToString(self):
        source50_ = self
        if source50_.is_EGState:
            d_759___mcc_h0_ = source50_.segNum
            d_760___mcc_h1_ = source50_.st
            d_761_st_ = d_760___mcc_h1_
            d_762_segNum_ = d_759___mcc_h0_
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "("))) + (Int.default__.NatToString(d_762_segNum_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", [")))) + (StackElement.default__.StackToString(d_761_st_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "])")))
        elif True:
            d_763___mcc_h2_ = source50_.msg
            d_764_msg_ = d_763___mcc_h2_
            return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorGState("))) + (d_764_msg_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

    def StackToHTML(self):
        if (len((self).st)) == (0):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif True:
            d_765_o_ = GState.StackToHTMLHelper((self).st)
            return _dafny.SeqWithoutIsStrInference((d_765_o_)[:(len(d_765_o_)) - (1):])

    @staticmethod
    def StackToHTMLHelper(s):
        d_766___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_766___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_766___accumulator_ = (d_766___accumulator_) + ((((s)[0]).ToHTML()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ","))))
                    in91_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in91_
                    raise _dafny.TailCall()
                break

    def IsBounded(self, n):
        return ((self).is_ErrorGState) or (((self).is_EGState) and (((self).segNum) < (n)))


class GState_EGState(GState, NamedTuple('EGState', [('segNum', Any), ('st', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGState.GState.EGState({_dafny.string_of(self.segNum)}, {_dafny.string_of(self.st)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GState_EGState) and self.segNum == __o.segNum and self.st == __o.st
    def __hash__(self) -> int:
        return super().__hash__()

class GState_ErrorGState(GState, NamedTuple('ErrorGState', [('msg', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGState.GState.ErrorGState({self.msg.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GState_ErrorGState) and self.msg == __o.msg
    def __hash__(self) -> int:
        return super().__hash__()

