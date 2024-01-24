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
import CFGState
import ProofObject

# Module: PrettyIns

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def PrintInstructionToDafny(i, src, tgt):
        if (((i).op).opcode) == (0):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Stop(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (1):
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
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Lt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (17):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Gt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (18):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SLt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (19):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SGt(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (20):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Eq(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (21):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := IsZero(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (22):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := And(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (23):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Or(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (24):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Xor(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (25):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Not(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (26):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Byte(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (27):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Shl(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (28):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Shr(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (29):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Sar(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (32):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Keccak256(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (48):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Address(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (49):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Balance(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (50):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Origin(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (51):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Caller(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (52):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallValue(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (53):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallDataLoad(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (54):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallDataSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (55):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallDataCopy(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (56):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CodeSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (57):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CodeCopy(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (58):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := GasPrice(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (59):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ExtCodeSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (60):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ExtCodeCopy(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (61):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ReturnDataSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (62):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ReturnDataCopy(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (63):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ExtCodeHash(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (64):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := BlockHash(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (65):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Coinbase(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (66):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Timestamp(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (67):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Number(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (68):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Difficulty(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (69):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := GasLimit(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (70):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := ChainID(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (71):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SelfBalance(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (72):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := BaseFee(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (80):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Pop(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (81):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MLoad(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (82):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MStore(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (83):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MStore8(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (84):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SLoad(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (85):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SStore(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (86):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Jump(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (87):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := JumpI(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (92):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := RJump(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (93):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := RJumpI(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (94):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := RJumpV(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (88):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PC(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (89):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := MSize(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (90):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Gas(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (91):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := JumpDest(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (95):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Push0(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (96):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 1, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (97):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 2, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (98):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 3, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (99):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 4, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (100):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 5, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (101):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 6, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (102):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 7, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (103):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 8, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (104):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 9, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (105):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 10, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (106):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 11, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (107):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 12, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (108):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 13, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (109):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 14, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (110):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 15, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (111):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 16, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (112):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 17, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (113):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 18, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (114):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 19, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (115):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 20, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (116):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 21, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (117):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 22, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (118):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 23, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (119):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 24, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (120):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 25, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (121):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 26, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (122):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 27, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (123):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 28, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (124):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 29, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (125):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 30, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (126):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 31, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (127):
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := PushN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 32, 0x")))) + ((i).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
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
        elif (((i).op).opcode) == (160):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 0);")))
        elif (((i).op).opcode) == (161):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 1);")))
        elif (((i).op).opcode) == (162):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 2);")))
        elif (((i).op).opcode) == (163):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 3);")))
        elif (((i).op).opcode) == (164):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := LogN(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", 4);")))
        elif (((i).op).opcode) == (241):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Call(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (242):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := CallCode(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (243):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Return(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (244):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := DelegateCall(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (245):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Create2(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (250):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := StaticCall(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (253):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Revert(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (255):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := SelfDestruct(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ");")))
        elif (((i).op).opcode) == (254):
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "var s"))) + (default__.DecToString(tgt))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " := Stop(s")))) + (default__.DecToString(src))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "); // Invalid instruction:\n")))
        elif True:
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unknown instruction:"))) + (((i).op).name)

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
        d_780___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) < (10):
                    return (_dafny.SeqWithoutIsStrInference([default__.DecToChar(n)])) + (d_780___accumulator_)
                elif True:
                    d_780___accumulator_ = (_dafny.SeqWithoutIsStrInference([default__.DecToChar(_dafny.euclidian_modulus(n, 10))])) + (d_780___accumulator_)
                    in92_ = _dafny.euclidian_division(n, 10)
                    n = in92_
                    raise _dafny.TailCall()
                break

