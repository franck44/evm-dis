import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_

# Module: Int

class default__:
    def  __init__(self):
        pass

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

class u8:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class u16:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class u32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class u64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class u128:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class u256:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
