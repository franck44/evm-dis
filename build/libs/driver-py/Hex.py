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

# Module: Hex

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsHexString(s):
        def lambda0_(forall_var_0_):
            d_0_k_: int = forall_var_0_
            return not (((0) <= (d_0_k_)) and ((d_0_k_) < (len(s)))) or (default__.IsHex((s)[d_0_k_]))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda0_)

    @staticmethod
    def HexToU8(s):
        source0_ = (default__.HexVal((s)[0]), default__.HexVal((s)[1]))
        if True:
            d_00_ = source0_[0]
            if d_00_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_10_ = source0_[1]
            if d_10_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_01_ = source0_[0]
            d_0_v1_ = d_01_.v
            d_11_ = source0_[1]
            d_1_v2_ = d_11_.v
            return MiscTypes.Option_Some(((Int.default__.TWO__4) * (d_0_v1_)) + (d_1_v2_))

    @staticmethod
    def HexToU16(s):
        source0_ = (default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:])), default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[2::])))
        if True:
            d_00_ = source0_[0]
            if d_00_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_10_ = source0_[1]
            if d_10_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_01_ = source0_[0]
            d_0_v1_ = d_01_.v
            d_11_ = source0_[1]
            d_1_v2_ = d_11_.v
            return MiscTypes.Option_Some(((Int.default__.TWO__8) * (d_0_v1_)) + (d_1_v2_))

    @staticmethod
    def HexToU32(s):
        source0_ = (default__.HexToU16(_dafny.SeqWithoutIsStrInference((s)[:4:])), default__.HexToU16(_dafny.SeqWithoutIsStrInference((s)[4::])))
        if True:
            d_00_ = source0_[0]
            if d_00_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_10_ = source0_[1]
            if d_10_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_01_ = source0_[0]
            d_0_v1_ = d_01_.v
            d_11_ = source0_[1]
            d_1_v2_ = d_11_.v
            return MiscTypes.Option_Some(((Int.default__.TWO__16) * (d_0_v1_)) + (d_1_v2_))

    @staticmethod
    def HexToU64(s):
        source0_ = (default__.HexToU32(_dafny.SeqWithoutIsStrInference((s)[:8:])), default__.HexToU32(_dafny.SeqWithoutIsStrInference((s)[8::])))
        if True:
            d_00_ = source0_[0]
            if d_00_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_10_ = source0_[1]
            if d_10_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_01_ = source0_[0]
            d_0_v1_ = d_01_.v
            d_11_ = source0_[1]
            d_1_v2_ = d_11_.v
            return MiscTypes.Option_Some(((Int.default__.TWO__32) * (d_0_v1_)) + (d_1_v2_))

    @staticmethod
    def HexToU128(s):
        source0_ = (default__.HexToU64(_dafny.SeqWithoutIsStrInference((s)[:16:])), default__.HexToU64(_dafny.SeqWithoutIsStrInference((s)[16::])))
        if True:
            d_00_ = source0_[0]
            if d_00_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_10_ = source0_[1]
            if d_10_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_01_ = source0_[0]
            d_0_v1_ = d_01_.v
            d_11_ = source0_[1]
            d_1_v2_ = d_11_.v
            return MiscTypes.Option_Some(((Int.default__.TWO__64) * (d_0_v1_)) + (d_1_v2_))

    @staticmethod
    def HexToU256(s):
        source0_ = (default__.HexToU128(_dafny.SeqWithoutIsStrInference((s)[:32:])), default__.HexToU128(_dafny.SeqWithoutIsStrInference((s)[32::])))
        if True:
            d_00_ = source0_[0]
            if d_00_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_10_ = source0_[1]
            if d_10_.is_None:
                return MiscTypes.Option_None()
        if True:
            d_01_ = source0_[0]
            d_0_v1_ = d_01_.v
            d_11_ = source0_[1]
            d_1_v2_ = d_11_.v
            return MiscTypes.Option_Some(((Int.default__.TWO__128) * (d_0_v1_)) + (d_1_v2_))

    @staticmethod
    def U8ToHex(n):
        return (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_division(n, Int.default__.TWO__4))])) + (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_modulus(n, Int.default__.TWO__4))]))

    @staticmethod
    def HexHelper(s):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (default__.U8ToHex((s)[0]))
                    in0_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def U16ToHex(n):
        return (default__.U8ToHex(_dafny.euclidian_division(n, Int.default__.TWO__8))) + (default__.U8ToHex(_dafny.euclidian_modulus(n, Int.default__.TWO__8)))

    @staticmethod
    def U32ToHex(n):
        return (default__.U16ToHex(_dafny.euclidian_division(n, Int.default__.TWO__16))) + (default__.U16ToHex(_dafny.euclidian_modulus(n, Int.default__.TWO__16)))

    @staticmethod
    def U64ToHex(n):
        return (default__.U32ToHex(_dafny.euclidian_division(n, Int.default__.TWO__32))) + (default__.U32ToHex(_dafny.euclidian_modulus(n, Int.default__.TWO__32)))

    @staticmethod
    def U128ToHex(n):
        return (default__.U64ToHex(_dafny.euclidian_division(n, Int.default__.TWO__64))) + (default__.U64ToHex(_dafny.euclidian_modulus(n, Int.default__.TWO__64)))

    @staticmethod
    def U256ToHex(n):
        return (default__.U128ToHex(_dafny.euclidian_division(n, Int.default__.TWO__128))) + (default__.U128ToHex(_dafny.euclidian_modulus(n, Int.default__.TWO__128)))

    @staticmethod
    def NatToHex(n):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) < (16):
                    return (_dafny.SeqWithoutIsStrInference([default__.DecToHex(n)])) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_modulus(n, 16))])) + (d_0___accumulator_)
                    in0_ = _dafny.euclidian_division(n, 16)
                    n = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def HexVal(c):
        source0_ = c
        if True:
            if (source0_) == (_dafny.CodePoint('0')):
                return MiscTypes.Option_Some(0)
        if True:
            if (source0_) == (_dafny.CodePoint('1')):
                return MiscTypes.Option_Some(1)
        if True:
            if (source0_) == (_dafny.CodePoint('2')):
                return MiscTypes.Option_Some(2)
        if True:
            if (source0_) == (_dafny.CodePoint('3')):
                return MiscTypes.Option_Some(3)
        if True:
            if (source0_) == (_dafny.CodePoint('4')):
                return MiscTypes.Option_Some(4)
        if True:
            if (source0_) == (_dafny.CodePoint('5')):
                return MiscTypes.Option_Some(5)
        if True:
            if (source0_) == (_dafny.CodePoint('6')):
                return MiscTypes.Option_Some(6)
        if True:
            if (source0_) == (_dafny.CodePoint('7')):
                return MiscTypes.Option_Some(7)
        if True:
            if (source0_) == (_dafny.CodePoint('8')):
                return MiscTypes.Option_Some(8)
        if True:
            if (source0_) == (_dafny.CodePoint('9')):
                return MiscTypes.Option_Some(9)
        if True:
            if (source0_) == (_dafny.CodePoint('a')):
                return MiscTypes.Option_Some(10)
        if True:
            if (source0_) == (_dafny.CodePoint('A')):
                return MiscTypes.Option_Some(10)
        if True:
            if (source0_) == (_dafny.CodePoint('b')):
                return MiscTypes.Option_Some(11)
        if True:
            if (source0_) == (_dafny.CodePoint('B')):
                return MiscTypes.Option_Some(11)
        if True:
            if (source0_) == (_dafny.CodePoint('c')):
                return MiscTypes.Option_Some(12)
        if True:
            if (source0_) == (_dafny.CodePoint('C')):
                return MiscTypes.Option_Some(12)
        if True:
            if (source0_) == (_dafny.CodePoint('d')):
                return MiscTypes.Option_Some(13)
        if True:
            if (source0_) == (_dafny.CodePoint('D')):
                return MiscTypes.Option_Some(13)
        if True:
            if (source0_) == (_dafny.CodePoint('e')):
                return MiscTypes.Option_Some(14)
        if True:
            if (source0_) == (_dafny.CodePoint('E')):
                return MiscTypes.Option_Some(14)
        if True:
            if (source0_) == (_dafny.CodePoint('f')):
                return MiscTypes.Option_Some(15)
        if True:
            if (source0_) == (_dafny.CodePoint('F')):
                return MiscTypes.Option_Some(15)
        if True:
            return MiscTypes.Option_None()

    @staticmethod
    def DecToHex(n):
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
            if (source0_) == (9):
                return _dafny.CodePoint('9')
        if True:
            if (source0_) == (10):
                return _dafny.CodePoint('a')
        if True:
            if (source0_) == (11):
                return _dafny.CodePoint('b')
        if True:
            if (source0_) == (12):
                return _dafny.CodePoint('c')
        if True:
            if (source0_) == (13):
                return _dafny.CodePoint('d')
        if True:
            if (source0_) == (14):
                return _dafny.CodePoint('e')
        if True:
            return _dafny.CodePoint('f')

    @staticmethod
    def IsHex(c):
        return ((((_dafny.CodePoint('0')) <= (c)) and ((c) <= (_dafny.CodePoint('9')))) or (((_dafny.CodePoint('a')) <= (c)) and ((c) <= (_dafny.CodePoint('f'))))) or (((_dafny.CodePoint('A')) <= (c)) and ((c) <= (_dafny.CodePoint('F'))))

