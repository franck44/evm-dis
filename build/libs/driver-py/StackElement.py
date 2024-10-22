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

# Module: StackElement

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def StackToString(s):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Ø")))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + ((((s)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ","))))
                    in0_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in0_
                    raise _dafny.TailCall()
                break


class StackElem:
    @classmethod
    def default(cls, ):
        return lambda: StackElem_Value(int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Value(self) -> bool:
        return isinstance(self, StackElem_Value)
    @property
    def is_Random(self) -> bool:
        return isinstance(self, StackElem_Random)
    def ToString(self):
        source0_ = self
        if True:
            if source0_.is_Value:
                d_0_v_ = source0_.v
                return (((Int.default__.NatToString(d_0_v_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(0x")))) + (Hex.default__.NatToHex(d_0_v_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
        if True:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "?"))

    def ToHTML(self):
        source0_ = self
        if True:
            if source0_.is_Value:
                d_0_v_ = source0_.v
                return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(0x"))) + (Hex.default__.NatToHex(d_0_v_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
        if True:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "?"))

    def Extract(self):
        return (self).v


class StackElem_Value(StackElem, NamedTuple('Value', [('v', Any)])):
    def __dafnystr__(self) -> str:
        return f'StackElement.StackElem.Value({_dafny.string_of(self.v)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, StackElem_Value) and self.v == __o.v
    def __hash__(self) -> int:
        return super().__hash__()

class StackElem_Random(StackElem, NamedTuple('Random', [('s', Any)])):
    def __dafnystr__(self) -> str:
        return f'StackElement.StackElem.Random({self.s.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, StackElem_Random) and self.s == __o.s
    def __hash__(self) -> int:
        return super().__hash__()

