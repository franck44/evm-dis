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

# Module: Hex

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def HexToU8(s):
        source0_ = (default__.HexVal((s)[0]), default__.HexVal((s)[1]))
        d_1___mcc_h0_ = source0_[0]
        d_2___mcc_h1_ = source0_[1]
        source1_ = d_1___mcc_h0_
        if source1_.is_None:
            source2_ = d_2___mcc_h1_
            if source2_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_3___mcc_h2_ = source2_.v
                return MiscTypes.Option_None()
        elif True:
            d_4___mcc_h4_ = source1_.v
            source3_ = d_2___mcc_h1_
            if source3_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_5___mcc_h6_ = source3_.v
                d_6_v2_ = d_5___mcc_h6_
                d_7_v1_ = d_4___mcc_h4_
                return MiscTypes.Option_Some(((16) * (d_7_v1_)) + (d_6_v2_))

    @staticmethod
    def HexVal(c):
        if (c) == (_dafny.CodePoint('0')):
            return MiscTypes.Option_Some(0)
        elif (c) == (_dafny.CodePoint('1')):
            return MiscTypes.Option_Some(1)
        elif (c) == (_dafny.CodePoint('2')):
            return MiscTypes.Option_Some(2)
        elif (c) == (_dafny.CodePoint('3')):
            return MiscTypes.Option_Some(3)
        elif (c) == (_dafny.CodePoint('4')):
            return MiscTypes.Option_Some(4)
        elif (c) == (_dafny.CodePoint('5')):
            return MiscTypes.Option_Some(5)
        elif (c) == (_dafny.CodePoint('6')):
            return MiscTypes.Option_Some(6)
        elif (c) == (_dafny.CodePoint('7')):
            return MiscTypes.Option_Some(7)
        elif (c) == (_dafny.CodePoint('8')):
            return MiscTypes.Option_Some(8)
        elif (c) == (_dafny.CodePoint('9')):
            return MiscTypes.Option_Some(9)
        elif (c) == (_dafny.CodePoint('a')):
            return MiscTypes.Option_Some(10)
        elif (c) == (_dafny.CodePoint('A')):
            return MiscTypes.Option_Some(10)
        elif (c) == (_dafny.CodePoint('b')):
            return MiscTypes.Option_Some(11)
        elif (c) == (_dafny.CodePoint('B')):
            return MiscTypes.Option_Some(11)
        elif (c) == (_dafny.CodePoint('c')):
            return MiscTypes.Option_Some(12)
        elif (c) == (_dafny.CodePoint('C')):
            return MiscTypes.Option_Some(12)
        elif (c) == (_dafny.CodePoint('d')):
            return MiscTypes.Option_Some(13)
        elif (c) == (_dafny.CodePoint('D')):
            return MiscTypes.Option_Some(13)
        elif (c) == (_dafny.CodePoint('e')):
            return MiscTypes.Option_Some(14)
        elif (c) == (_dafny.CodePoint('E')):
            return MiscTypes.Option_Some(14)
        elif (c) == (_dafny.CodePoint('f')):
            return MiscTypes.Option_Some(15)
        elif (c) == (_dafny.CodePoint('F')):
            return MiscTypes.Option_Some(15)
        elif True:
            return MiscTypes.Option_None()

