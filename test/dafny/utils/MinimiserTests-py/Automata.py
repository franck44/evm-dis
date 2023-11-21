import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes
import SeqOfSets
import PartitionMod

# Module: Automata


class ValidAuto:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Auto_Auto(0, _dafny.Map({}))

class Auto:
    @classmethod
    def default(cls, ):
        return lambda: Auto_Auto(int(0), _dafny.Map({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Auto(self) -> bool:
        return isinstance(self, Auto_Auto)
    def IsValid(self):
        def lambda7_(forall_var_3_):
            d_34_k_: tuple = forall_var_3_
            return not ((d_34_k_) in ((self).transitions)) or ((((self).transitions)[d_34_k_]) < ((self).numStates))

        return _dafny.quantifier(((self).transitions).keys.Elements, True, lambda7_)

    def Succ(self, s, l):
        if ((s, l)) in ((self).transitions):
            return MiscTypes.Option_Some(((self).transitions)[(s, l)])
        elif True:
            return MiscTypes.Option_None()


class Auto_Auto(Auto, NamedTuple('Auto', [('numStates', Any), ('transitions', Any)])):
    def __dafnystr__(self) -> str:
        return f'Automata.Auto.Auto({_dafny.string_of(self.numStates)}, {_dafny.string_of(self.transitions)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Auto_Auto) and self.numStates == __o.numStates and self.transitions == __o.transitions
    def __hash__(self) -> int:
        return super().__hash__()

