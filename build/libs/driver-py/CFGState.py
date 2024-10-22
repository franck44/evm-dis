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
import SegBuilder as SegBuilder

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
        source0_ = self
        if True:
            if source0_.is_EGState:
                d_0_segNum_ = source0_.segNum
                d_1_st_ = source0_.st
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "("))) + (Int.default__.NatToString(d_0_segNum_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", [")))) + (StackElement.default__.StackToString(d_1_st_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "])")))
        if True:
            d_2_msg_ = source0_.msg
            return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorGState("))) + (d_2_msg_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

    def StackToHTML(self):
        if (len((self).st)) == (0):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif True:
            d_0_o_ = GState.StackToHTMLHelper((self).st)
            return _dafny.SeqWithoutIsStrInference((d_0_o_)[:(len(d_0_o_)) - (1):])

    @staticmethod
    def StackToHTMLHelper(s):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + ((((s)[0]).ToHTML()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ","))))
                    in0_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in0_
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

