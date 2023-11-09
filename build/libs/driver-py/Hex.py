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

# Module: Hex

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def HexToU8(s):
        source1_ = (default__.HexVal((s)[0]), default__.HexVal((s)[1]))
        d_80___mcc_h0_ = source1_[0]
        d_81___mcc_h1_ = source1_[1]
        source2_ = d_80___mcc_h0_
        if source2_.is_None:
            source3_ = d_81___mcc_h1_
            if source3_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_82___mcc_h2_ = source3_.v
                return MiscTypes.Option_None()
        elif True:
            d_83___mcc_h4_ = source2_.v
            source4_ = d_81___mcc_h1_
            if source4_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_84___mcc_h6_ = source4_.v
                d_85_v2_ = d_84___mcc_h6_
                d_86_v1_ = d_83___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__4) * (d_86_v1_)) + (d_85_v2_))

    @staticmethod
    def HexToU16(s):
        source5_ = (default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:])), default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[2::])))
        d_87___mcc_h0_ = source5_[0]
        d_88___mcc_h1_ = source5_[1]
        source6_ = d_87___mcc_h0_
        if source6_.is_None:
            source7_ = d_88___mcc_h1_
            if source7_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_89___mcc_h2_ = source7_.v
                return MiscTypes.Option_None()
        elif True:
            d_90___mcc_h4_ = source6_.v
            source8_ = d_88___mcc_h1_
            if source8_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_91___mcc_h6_ = source8_.v
                d_92_v2_ = d_91___mcc_h6_
                d_93_v1_ = d_90___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__8) * (d_93_v1_)) + (d_92_v2_))

    @staticmethod
    def HexToU32(s):
        source9_ = (default__.HexToU16(_dafny.SeqWithoutIsStrInference((s)[:4:])), default__.HexToU16(_dafny.SeqWithoutIsStrInference((s)[4::])))
        d_94___mcc_h0_ = source9_[0]
        d_95___mcc_h1_ = source9_[1]
        source10_ = d_94___mcc_h0_
        if source10_.is_None:
            source11_ = d_95___mcc_h1_
            if source11_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_96___mcc_h2_ = source11_.v
                return MiscTypes.Option_None()
        elif True:
            d_97___mcc_h4_ = source10_.v
            source12_ = d_95___mcc_h1_
            if source12_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_98___mcc_h6_ = source12_.v
                d_99_v2_ = d_98___mcc_h6_
                d_100_v1_ = d_97___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__16) * (d_100_v1_)) + (d_99_v2_))

    @staticmethod
    def HexToU64(s):
        source13_ = (default__.HexToU32(_dafny.SeqWithoutIsStrInference((s)[:8:])), default__.HexToU32(_dafny.SeqWithoutIsStrInference((s)[8::])))
        d_101___mcc_h0_ = source13_[0]
        d_102___mcc_h1_ = source13_[1]
        source14_ = d_101___mcc_h0_
        if source14_.is_None:
            source15_ = d_102___mcc_h1_
            if source15_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_103___mcc_h2_ = source15_.v
                return MiscTypes.Option_None()
        elif True:
            d_104___mcc_h4_ = source14_.v
            source16_ = d_102___mcc_h1_
            if source16_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_105___mcc_h6_ = source16_.v
                d_106_v2_ = d_105___mcc_h6_
                d_107_v1_ = d_104___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__32) * (d_107_v1_)) + (d_106_v2_))

    @staticmethod
    def HexToU128(s):
        source17_ = (default__.HexToU64(_dafny.SeqWithoutIsStrInference((s)[:16:])), default__.HexToU64(_dafny.SeqWithoutIsStrInference((s)[16::])))
        d_108___mcc_h0_ = source17_[0]
        d_109___mcc_h1_ = source17_[1]
        source18_ = d_108___mcc_h0_
        if source18_.is_None:
            source19_ = d_109___mcc_h1_
            if source19_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_110___mcc_h2_ = source19_.v
                return MiscTypes.Option_None()
        elif True:
            d_111___mcc_h4_ = source18_.v
            source20_ = d_109___mcc_h1_
            if source20_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_112___mcc_h6_ = source20_.v
                d_113_v2_ = d_112___mcc_h6_
                d_114_v1_ = d_111___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__64) * (d_114_v1_)) + (d_113_v2_))

    @staticmethod
    def HexToU256(s):
        source21_ = (default__.HexToU128(_dafny.SeqWithoutIsStrInference((s)[:32:])), default__.HexToU128(_dafny.SeqWithoutIsStrInference((s)[32::])))
        d_115___mcc_h0_ = source21_[0]
        d_116___mcc_h1_ = source21_[1]
        source22_ = d_115___mcc_h0_
        if source22_.is_None:
            source23_ = d_116___mcc_h1_
            if source23_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_117___mcc_h2_ = source23_.v
                return MiscTypes.Option_None()
        elif True:
            d_118___mcc_h4_ = source22_.v
            source24_ = d_116___mcc_h1_
            if source24_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_119___mcc_h6_ = source24_.v
                d_120_v2_ = d_119___mcc_h6_
                d_121_v1_ = d_118___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__128) * (d_121_v1_)) + (d_120_v2_))

    @staticmethod
    def U8ToHex(n):
        return (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_division(n, Int.default__.TWO__4))])) + (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_modulus(n, Int.default__.TWO__4))]))

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
        d_122___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) < (16):
                    return (_dafny.SeqWithoutIsStrInference([default__.DecToHex(n)])) + (d_122___accumulator_)
                elif True:
                    d_122___accumulator_ = (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_modulus(n, 16))])) + (d_122___accumulator_)
                    in10_ = _dafny.euclidian_division(n, 16)
                    n = in10_
                    raise _dafny.TailCall()
                break

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

    @staticmethod
    def DecToHex(n):
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
        elif (n) == (9):
            return _dafny.CodePoint('9')
        elif (n) == (10):
            return _dafny.CodePoint('a')
        elif (n) == (11):
            return _dafny.CodePoint('b')
        elif (n) == (12):
            return _dafny.CodePoint('c')
        elif (n) == (13):
            return _dafny.CodePoint('d')
        elif (n) == (14):
            return _dafny.CodePoint('e')
        elif True:
            return _dafny.CodePoint('f')

    @staticmethod
    def IsHex(c):
        return ((((_dafny.CodePoint('0')) <= (c)) and ((c) <= (_dafny.CodePoint('9')))) or (((_dafny.CodePoint('a')) <= (c)) and ((c) <= (_dafny.CodePoint('f'))))) or (((_dafny.CodePoint('A')) <= (c)) and ((c) <= (_dafny.CodePoint('F'))))

