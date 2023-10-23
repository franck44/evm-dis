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
            d_11_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            default__.PrintInstructions(d_11_x_)

    @staticmethod
    def PrintInstructions(s):
        while True:
            with _dafny.label():
                if (len(s)) > (0):
                    d_12_formattedAddress_: _dafny.Seq
                    d_12_formattedAddress_ = (Hex.default__.U32ToHex(((s)[0]).address) if (((s)[0]).address) < (Int.default__.TWO__32) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "OutofRange")))
                    _dafny.print((d_12_formattedAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": "))).VerbatimString(False))
                    _dafny.print((((s)[0]).ToString()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in6_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in6_
                    raise _dafny.TailCall()
                break

