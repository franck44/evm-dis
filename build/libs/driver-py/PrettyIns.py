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
import StackElement
import WeakPre
import State
import Instructions
import BinaryDecoder
import LinSegments
import Splitter
import SegBuilder
import ProofObject

# Module: PrettyIns

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def PrintInstructionToDafny(i, src, tgt):
        if (((i).op).opcode) == (1):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Add(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (2):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Mul(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (3):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Sub(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (4):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Div(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (5):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SDiv(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (6):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Mod(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (7):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SMod(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (8):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := AddMod(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (9):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MulMod(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (10):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Exp(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (11):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SignExtended(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (16):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Bytecode.Lt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (80):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Pop(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (82):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Bytecode.MStore(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (86):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Jump(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (87):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := JumpI(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (91):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := JumpDest(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (95):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Push0(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (96):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Push1(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (128):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 1);")))
        elif (((i).op).opcode) == (129):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 2);")))
        elif (((i).op).opcode) == (130):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 3);")))
        elif (((i).op).opcode) == (131):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 4);")))
        elif (((i).op).opcode) == (132):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 5);")))
        elif (((i).op).opcode) == (133):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 6);")))
        elif (((i).op).opcode) == (134):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 7);")))
        elif (((i).op).opcode) == (135):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 8);")))
        elif (((i).op).opcode) == (136):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 9);")))
        elif (((i).op).opcode) == (137):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 10);")))
        elif (((i).op).opcode) == (138):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 11);")))
        elif (((i).op).opcode) == (139):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 12);")))
        elif (((i).op).opcode) == (140):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 13);")))
        elif (((i).op).opcode) == (141):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 14);")))
        elif (((i).op).opcode) == (142):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 15);")))
        elif (((i).op).opcode) == (143):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 16);")))
        elif (((i).op).opcode) == (144):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 1);")))
        elif (((i).op).opcode) == (145):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 2);")))
        elif (((i).op).opcode) == (146):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 3);")))
        elif (((i).op).opcode) == (147):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 4);")))
        elif (((i).op).opcode) == (148):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 5);")))
        elif (((i).op).opcode) == (149):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 6);")))
        elif (((i).op).opcode) == (150):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 7);")))
        elif (((i).op).opcode) == (151):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 8);")))
        elif (((i).op).opcode) == (152):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 9);")))
        elif (((i).op).opcode) == (153):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 10);")))
        elif (((i).op).opcode) == (154):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 11);")))
        elif (((i).op).opcode) == (155):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 12);")))
        elif (((i).op).opcode) == (156):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 13);")))
        elif (((i).op).opcode) == (157):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 14);")))
        elif (((i).op).opcode) == (158):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 15);")))
        elif (((i).op).opcode) == (159):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 16);")))
        elif (((i).op).opcode) == (243):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Return(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif True:
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unknwon instruction:"))) + (((i).op).name)

    @staticmethod
    def DecToChar(n):
        if (n) == (0):
            return _dafny.CodePoint('0')
        elif (n) == (1):
            return _dafny.CodePoint('1')
        elif (n) == (2):
            return _dafny.CodePoint('2')
        elif (n) == (3):
            return _dafny.CodePoint('3')
        elif (n) == (4):
            return _dafny.CodePoint('4')
        elif (n) == (5):
            return _dafny.CodePoint('5')
        elif (n) == (6):
            return _dafny.CodePoint('6')
        elif (n) == (7):
            return _dafny.CodePoint('7')
        elif (n) == (8):
            return _dafny.CodePoint('8')
        elif True:
            return _dafny.CodePoint('9')

    @staticmethod
    def DecToString(n):
        d_630___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) < (10):
                    return (_dafny.SeqWithoutIsStrInference([default__.DecToChar(n)])) + (d_630___accumulator_)
                elif True:
                    d_630___accumulator_ = (_dafny.SeqWithoutIsStrInference([default__.DecToChar(_dafny.euclidian_modulus(n, 10))])) + (d_630___accumulator_)
                    in71_ = _dafny.euclidian_division(n, 10)
                    n = in71_
                    raise _dafny.TailCall()
                break

