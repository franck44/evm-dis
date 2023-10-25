import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Int

# Module: MiscTypes


class Option:
    @classmethod
    def default(cls, ):
        return lambda: Option_None()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_None(self) -> bool:
        return isinstance(self, Option_None)
    @property
    def is_Some(self) -> bool:
        return isinstance(self, Option_Some)
    def Extract(self):
        return (self).v


class Option_None(Option, NamedTuple('None_', [])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Option.None'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_None)
    def __hash__(self) -> int:
        return super().__hash__()

class Option_Some(Option, NamedTuple('Some', [('v', Any)])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Option.Some({_dafny.string_of(self.v)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_Some) and self.v == __o.v
    def __hash__(self) -> int:
        return super().__hash__()


class Either:
    @classmethod
    def default(cls, default_T):
        return lambda: Either_Left(default_T())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Left(self) -> bool:
        return isinstance(self, Either_Left)
    @property
    def is_Right(self) -> bool:
        return isinstance(self, Either_Right)
    def Left(self):
        return (self).l

    def Right(self):
        return (self).r


class Either_Left(Either, NamedTuple('Left', [('l', Any)])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Either.Left({_dafny.string_of(self.l)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Either_Left) and self.l == __o.l
    def __hash__(self) -> int:
        return super().__hash__()

class Either_Right(Either, NamedTuple('Right', [('r', Any)])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Either.Right({_dafny.string_of(self.r)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Either_Right) and self.r == __o.r
    def __hash__(self) -> int:
        return super().__hash__()

