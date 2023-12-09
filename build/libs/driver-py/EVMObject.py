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
import ProofObject
import PrettyIns
import PrettyPrinters

# Module: EVMObject

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def CollectJumpDests(xs):
        d_807___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_807___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_807___accumulator_ = (d_807___accumulator_) + (((xs)[0]).CollectJumpDest(((xs)[0]).Ins()))
                    in83_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in83_
                    raise _dafny.TailCall()
                break


class ValidEVMObj:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return EVMObj_EVMObj(_dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))

class EVMObj:
    @classmethod
    def default(cls, ):
        return lambda: EVMObj_EVMObj(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_EVMObj(self) -> bool:
        return isinstance(self, EVMObj_EVMObj)
    def IsValid(self):
        return ((self).jumpDests) == (default__.CollectJumpDests((self).xs))

    def Size(self, ls):
        d_808___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (len(ls)) == (0):
                    return (0) + (d_808___accumulator_)
                elif True:
                    d_808___accumulator_ = (d_808___accumulator_) + (((ls)[0]).Size(((ls)[0]).Ins()))
                    in84_ = _this
                    in85_ = _dafny.SeqWithoutIsStrInference((ls)[1::])
                    _this = in84_
                    
                    ls = in85_
                    raise _dafny.TailCall()
                break


class EVMObj_EVMObj(EVMObj, NamedTuple('EVMObj', [('xs', Any), ('jumpDests', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMObject.EVMObj.EVMObj({_dafny.string_of(self.xs)}, {_dafny.string_of(self.jumpDests)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, EVMObj_EVMObj) and self.xs == __o.xs and self.jumpDests == __o.jumpDests
    def __hash__(self) -> int:
        return super().__hash__()

