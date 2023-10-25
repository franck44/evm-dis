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
import Instructions
import BinaryDecoder
import Splitter
import SegBuilder

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
            d_97_x_: _dafny.Seq
            d_97_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            default__.PrintInstructions(d_97_x_)

    @staticmethod
    def Main2(args):
        if (len(args)) < (2):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Expected 1 arguments, got "))).VerbatimString(False))
            _dafny.print(_dafny.string_of((len(args)) - (1)))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        elif True:
            d_98_x_: _dafny.Seq
            d_98_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            default__.PrintInstructions(d_98_x_)
            d_99_y_: _dafny.Seq
            d_99_y_ = Splitter.default__.SplitUpToTerminal(d_98_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
            default__.PrintSegments(d_99_y_, 0)

    @staticmethod
    def PrintInstructions(s):
        while True:
            with _dafny.label():
                if (len(s)) > (0):
                    d_100_formattedAddress_: _dafny.Seq
                    d_100_formattedAddress_ = (Hex.default__.U32ToHex(((s)[0]).address) if (((s)[0]).address) < (Int.default__.TWO__32) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "OutofRange")))
                    _dafny.print((d_100_formattedAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": "))).VerbatimString(False))
                    _dafny.print((((s)[0]).ToString()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in25_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in25_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintSegments(xs, num):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(num))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_101_k_: MiscTypes.Option
                    d_101_k_ = ((xs)[0]).WeakestPreOperands(0)
                    d_102_l_: MiscTypes.Option
                    d_102_l_ = ((xs)[0]).WeakestPreCapacity(0)
                    if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMP/JUMPI: "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(SegBuilder.default__.JUMPResolver((xs)[0])))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Operands:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_101_k_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Capacity:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_102_l_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    default__.PrintInstructions(((xs)[0]).Ins())
                    in26_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in27_ = (num) + (1)
                    xs = in26_
                    num = in27_
                    raise _dafny.TailCall()
                break

