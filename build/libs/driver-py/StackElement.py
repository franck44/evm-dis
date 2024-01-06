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

# Module: StackElement

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def StackToString(s):
        d_136___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_136___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Ø")))
                elif True:
                    d_136___accumulator_ = (d_136___accumulator_) + ((((s)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ","))))
                    in18_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in18_
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
        source26_ = self
        if source26_.is_Value:
            d_137___mcc_h0_ = source26_.v
            d_138_v_ = d_137___mcc_h0_
            return (((Int.default__.NatToString(d_138_v_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(0x")))) + (Hex.default__.NatToHex(d_138_v_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
        elif True:
            d_139___mcc_h1_ = source26_.s
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

