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

# Module: StackElement


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

