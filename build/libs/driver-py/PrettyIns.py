import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import MiscTypes as MiscTypes
import Int as Int
import EVMConstants as EVMConstants
import EVMOpcodes as EVMOpcodes
import OpcodeDecoder as OpcodeDecoder
import Hex as Hex
import StackElement as StackElement
import WeakPre as WeakPre
import State as State
import EVMToolTips as EVMToolTips
import Instructions as Instructions
import BinaryDecoder as BinaryDecoder
import LinSegments as LinSegments
import Splitter as Splitter
import SegBuilder as SegBuilder
import CFGState as CFGState
import ProofObject as ProofObject

# Module: PrettyIns

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def PrintInstructionToDafny(i, src, tgt):
        source0_ = ((i).op).opcode
        if True:
            if (source0_) == (0):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Stop(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (1):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Add(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (2):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Mul(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (3):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Sub(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (4):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Div(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (5):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SDiv(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (6):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Mod(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (7):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SMod(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (8):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := AddMod(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (9):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MulMod(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (10):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Exp(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (11):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SignExtended(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (16):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Lt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (17):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Gt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (18):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SLt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (19):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SGt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (20):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Eq(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (21):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := IsZero(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (22):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := And(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (23):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Or(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (24):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Xor(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (25):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Not(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (26):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Byte(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (27):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Shl(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (28):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Shr(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (29):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Sar(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (32):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Keccak256(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (48):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Address(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (49):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Balance(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (50):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Origin(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (51):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Caller(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (52):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallValue(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (53):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallDataLoad(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (54):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallDataSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (55):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallDataCopy(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (56):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CodeSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (57):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CodeCopy(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (58):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := GasPrice(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (59):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ExtCodeSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (60):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ExtCodeCopy(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (61):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ReturnDataSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (62):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ReturnDataCopy(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (63):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ExtCodeHash(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (64):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := BlockHash(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (65):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Coinbase(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (66):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Timestamp(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (67):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Number(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (68):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Difficulty(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (69):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := GasLimit(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (70):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ChainID(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (71):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SelfBalance(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (72):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := BaseFee(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (80):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Pop(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (81):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MLoad(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (82):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MStore(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (83):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MStore8(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (84):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SLoad(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (85):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SStore(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (86):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Jump(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (87):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := JumpI(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (92):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := RJump(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (93):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := RJumpI(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (94):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := RJumpV(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (88):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PC(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (89):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (90):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Gas(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (91):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := JumpDest(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (95):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Push0(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (96):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 1, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (97):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 2, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (98):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 3, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (99):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 4, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (100):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 5, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (101):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 6, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (102):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 7, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (103):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 8, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (104):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 9, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (105):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 10, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (106):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 11, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (107):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 12, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (108):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 13, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (109):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 14, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (110):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 15, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (111):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 16, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (112):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 17, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (113):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 18, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (114):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 19, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (115):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 20, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (116):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 21, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (117):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 22, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (118):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 23, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (119):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 24, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (120):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 25, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (121):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 26, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (122):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 27, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (123):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 28, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (124):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 29, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (125):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 30, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (126):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 31, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (127):
                return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 32, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (128):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 1);")))
        if True:
            if (source0_) == (129):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 2);")))
        if True:
            if (source0_) == (130):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 3);")))
        if True:
            if (source0_) == (131):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 4);")))
        if True:
            if (source0_) == (132):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 5);")))
        if True:
            if (source0_) == (133):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 6);")))
        if True:
            if (source0_) == (134):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 7);")))
        if True:
            if (source0_) == (135):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 8);")))
        if True:
            if (source0_) == (136):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 9);")))
        if True:
            if (source0_) == (137):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 10);")))
        if True:
            if (source0_) == (138):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 11);")))
        if True:
            if (source0_) == (139):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 12);")))
        if True:
            if (source0_) == (140):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 13);")))
        if True:
            if (source0_) == (141):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 14);")))
        if True:
            if (source0_) == (142):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 15);")))
        if True:
            if (source0_) == (143):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Dup(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 16);")))
        if True:
            if (source0_) == (144):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 1);")))
        if True:
            if (source0_) == (145):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 2);")))
        if True:
            if (source0_) == (146):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 3);")))
        if True:
            if (source0_) == (147):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 4);")))
        if True:
            if (source0_) == (148):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 5);")))
        if True:
            if (source0_) == (149):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 6);")))
        if True:
            if (source0_) == (150):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 7);")))
        if True:
            if (source0_) == (151):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 8);")))
        if True:
            if (source0_) == (152):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 9);")))
        if True:
            if (source0_) == (153):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 10);")))
        if True:
            if (source0_) == (154):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 11);")))
        if True:
            if (source0_) == (155):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 12);")))
        if True:
            if (source0_) == (156):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 13);")))
        if True:
            if (source0_) == (157):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 14);")))
        if True:
            if (source0_) == (158):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 15);")))
        if True:
            if (source0_) == (159):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Swap(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 16);")))
        if True:
            if (source0_) == (160):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 0);")))
        if True:
            if (source0_) == (161):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 1);")))
        if True:
            if (source0_) == (162):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 2);")))
        if True:
            if (source0_) == (163):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 3);")))
        if True:
            if (source0_) == (164):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 4);")))
        if True:
            if (source0_) == (241):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Call(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (242):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallCode(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (243):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Return(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (244):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := DelegateCall(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (245):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Create2(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (250):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := StaticCall(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (253):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Revert(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (255):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SelfDestruct(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        if True:
            if (source0_) == (254):
                return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Stop(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "); // Invalid instruction:\n")))
        if True:
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unknown instruction:"))) + (((i).op).name)

    @staticmethod
    def DecToChar(n):
        source0_ = n
        if True:
            if (source0_) == (0):
                return _dafny.CodePoint('0')
        if True:
            if (source0_) == (1):
                return _dafny.CodePoint('1')
        if True:
            if (source0_) == (2):
                return _dafny.CodePoint('2')
        if True:
            if (source0_) == (3):
                return _dafny.CodePoint('3')
        if True:
            if (source0_) == (4):
                return _dafny.CodePoint('4')
        if True:
            if (source0_) == (5):
                return _dafny.CodePoint('5')
        if True:
            if (source0_) == (6):
                return _dafny.CodePoint('6')
        if True:
            if (source0_) == (7):
                return _dafny.CodePoint('7')
        if True:
            if (source0_) == (8):
                return _dafny.CodePoint('8')
        if True:
            return _dafny.CodePoint('9')

    @staticmethod
    def DecToString(n):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) < (10):
                    return (_dafny.SeqWithoutIsStrInference([default__.DecToChar(n)])) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (_dafny.SeqWithoutIsStrInference([default__.DecToChar(_dafny.euclidian_modulus(n, 10))])) + (d_0___accumulator_)
                    in0_ = _dafny.euclidian_division(n, 10)
                    n = in0_
                    raise _dafny.TailCall()
                break

