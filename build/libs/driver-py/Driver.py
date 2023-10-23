import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Int
import EVMOpcodes
import OpcodeDecoder
import MiscTypes
import Hex
import BinaryDecoder

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        if (len(args)) < (2):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Expected 1 arguments, got "))).VerbatimString(False))
            _dafny.print(_dafny.string_of((len(args)) - (1)))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        elif True:
            d_11_x_: _dafny.Seq
            d_11_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]))
            default__.PrintInstructions(d_11_x_)

    @staticmethod
    def PrintInstructions(s):
        while True:
            with _dafny.label():
                if (len(s)) > (0):
                    _dafny.print((((s)[0]).ToString()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in4_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in4_
                    raise _dafny.TailCall()
                break

