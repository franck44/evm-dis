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
import Automata
import Minimiser
import MinimiserTests

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Test____Main____(noArgsParameter__):
        d_75_success_: bool
        d_75_success_ = True
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MinimiserTests.Test1: "))).VerbatimString(False))
        try:
            if True:
                MinimiserTests.default__.Test1()
                if True:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PASSED\n"))).VerbatimString(False))
        except _dafny.HaltException as e:
            d_76_haltMessage_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, e.message))
            if True:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "FAILED\n	"))).VerbatimString(False))
                _dafny.print((d_76_haltMessage_).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                d_75_success_ = False
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MinimiserTests.Test8: "))).VerbatimString(False))
        try:
            if True:
                MinimiserTests.default__.Test8()
                if True:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PASSED\n"))).VerbatimString(False))
        except _dafny.HaltException as e:
            d_77_haltMessage_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, e.message))
            if True:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "FAILED\n	"))).VerbatimString(False))
                _dafny.print((d_77_haltMessage_).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                d_75_success_ = False
        if not(d_75_success_):
            raise _dafny.HaltException("test/dafny/utils/MinimiserTests.dfy(16,0): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Test failures occurred: see above.\n"))).VerbatimString(False))

