import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import MiscTypes as MiscTypes

# Module: Int

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Abs(x):
        if (x) >= (0):
            return x
        elif True:
            return (0) - (x)

    @staticmethod
    def Max(i1, i2):
        if (i1) >= (i2):
            return i1
        elif True:
            return i2

    @staticmethod
    def Min(i1, i2):
        if (i1) < (i2):
            return i1
        elif True:
            return i2

    @staticmethod
    def NatToString(n):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) < (10):
                    return (_dafny.SeqWithoutIsStrInference([default__.DigitToString(n)])) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (_dafny.SeqWithoutIsStrInference([default__.DigitToString(_dafny.euclidian_modulus(n, 10))])) + (d_0___accumulator_)
                    in0_ = _dafny.euclidian_division(n, 10)
                    n = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def IntToString(n):
        if (n) == (0):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0"))
        elif (n) > (0):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "+"))) + (default__.NatToString(n))
        elif True:
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-"))) + (default__.NatToString((0) - (n)))

    @staticmethod
    def DigitToString(n):
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
    def CharToDigit(c):
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
            return MiscTypes.Option_None()

    @staticmethod
    def IsNatNumber(s):
        while True:
            with _dafny.label():
                if (len(s)) == (1):
                    return (default__.CharToDigit((s)[0])).is_Some
                elif True:
                    source0_ = default__.CharToDigit((s)[0])
                    if True:
                        if source0_.is_Some:
                            d_0_v_ = source0_.v
                            in0_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                            s = in0_
                            raise _dafny.TailCall()
                    if True:
                        return False
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_0_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_0_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

    @_dafny.classproperty
    def TWO__8(instance):
        return 256
    @_dafny.classproperty
    def MAX__U8(instance):
        return (default__.TWO__8) - (1)
    @_dafny.classproperty
    def TWO__16(instance):
        return 65536
    @_dafny.classproperty
    def MAX__U16(instance):
        return (default__.TWO__16) - (1)
    @_dafny.classproperty
    def TWO__32(instance):
        return 4294967296
    @_dafny.classproperty
    def MAX__U32(instance):
        return (default__.TWO__32) - (1)
    @_dafny.classproperty
    def TWO__64(instance):
        return 18446744073709551616
    @_dafny.classproperty
    def MAX__U64(instance):
        return (default__.TWO__64) - (1)
    @_dafny.classproperty
    def TWO__128(instance):
        return 340282366920938463463374607431768211456
    @_dafny.classproperty
    def MAX__U128(instance):
        return (default__.TWO__128) - (1)
    @_dafny.classproperty
    def TWO__256(instance):
        return 115792089237316195423570985008687907853269984665640564039457584007913129639936
    @_dafny.classproperty
    def MAX__U256(instance):
        return (default__.TWO__256) - (1)
    @_dafny.classproperty
    def TWO__4(instance):
        return 16

class u8:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True

class u16:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True

class u32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True

class u64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True

class u128:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        d_0_i_: int = source__
        if System_.nat._Is(d_0_i_):
            return ((0) <= (d_0_i_)) and ((d_0_i_) <= (default__.MAX__U128))
        return False

class u256:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        d_1_i_: int = source__
        if System_.nat._Is(d_1_i_):
            return ((0) <= (d_1_i_)) and ((d_1_i_) <= (default__.MAX__U256))
        return False
