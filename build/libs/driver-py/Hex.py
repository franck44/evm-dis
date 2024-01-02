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

# Module: Hex

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsHexString(s):
        def lambda3_(forall_var_0_):
            d_90_k_: int = forall_var_0_
            return not (((0) <= (d_90_k_)) and ((d_90_k_) < (len(s)))) or (default__.IsHex((s)[d_90_k_]))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda3_)

    @staticmethod
    def HexToU8(s):
        source2_ = (default__.HexVal((s)[0]), default__.HexVal((s)[1]))
        d_91___mcc_h0_ = source2_[0]
        d_92___mcc_h1_ = source2_[1]
        source3_ = d_91___mcc_h0_
        if source3_.is_None:
            source4_ = d_92___mcc_h1_
            if source4_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_93___mcc_h2_ = source4_.v
                return MiscTypes.Option_None()
        elif True:
            d_94___mcc_h4_ = source3_.v
            source5_ = d_92___mcc_h1_
            if source5_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_95___mcc_h6_ = source5_.v
                d_96_v2_ = d_95___mcc_h6_
                d_97_v1_ = d_94___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__4) * (d_97_v1_)) + (d_96_v2_))

    @staticmethod
    def HexToU16(s):
        source6_ = (default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:])), default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[2::])))
        d_98___mcc_h0_ = source6_[0]
        d_99___mcc_h1_ = source6_[1]
        source7_ = d_98___mcc_h0_
        if source7_.is_None:
            source8_ = d_99___mcc_h1_
            if source8_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_100___mcc_h2_ = source8_.v
                return MiscTypes.Option_None()
        elif True:
            d_101___mcc_h4_ = source7_.v
            source9_ = d_99___mcc_h1_
            if source9_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_102___mcc_h6_ = source9_.v
                d_103_v2_ = d_102___mcc_h6_
                d_104_v1_ = d_101___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__8) * (d_104_v1_)) + (d_103_v2_))

    @staticmethod
    def HexToU32(s):
        source10_ = (default__.HexToU16(_dafny.SeqWithoutIsStrInference((s)[:4:])), default__.HexToU16(_dafny.SeqWithoutIsStrInference((s)[4::])))
        d_105___mcc_h0_ = source10_[0]
        d_106___mcc_h1_ = source10_[1]
        source11_ = d_105___mcc_h0_
        if source11_.is_None:
            source12_ = d_106___mcc_h1_
            if source12_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_107___mcc_h2_ = source12_.v
                return MiscTypes.Option_None()
        elif True:
            d_108___mcc_h4_ = source11_.v
            source13_ = d_106___mcc_h1_
            if source13_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_109___mcc_h6_ = source13_.v
                d_110_v2_ = d_109___mcc_h6_
                d_111_v1_ = d_108___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__16) * (d_111_v1_)) + (d_110_v2_))

    @staticmethod
    def HexToU64(s):
        source14_ = (default__.HexToU32(_dafny.SeqWithoutIsStrInference((s)[:8:])), default__.HexToU32(_dafny.SeqWithoutIsStrInference((s)[8::])))
        d_112___mcc_h0_ = source14_[0]
        d_113___mcc_h1_ = source14_[1]
        source15_ = d_112___mcc_h0_
        if source15_.is_None:
            source16_ = d_113___mcc_h1_
            if source16_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_114___mcc_h2_ = source16_.v
                return MiscTypes.Option_None()
        elif True:
            d_115___mcc_h4_ = source15_.v
            source17_ = d_113___mcc_h1_
            if source17_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_116___mcc_h6_ = source17_.v
                d_117_v2_ = d_116___mcc_h6_
                d_118_v1_ = d_115___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__32) * (d_118_v1_)) + (d_117_v2_))

    @staticmethod
    def HexToU128(s):
        source18_ = (default__.HexToU64(_dafny.SeqWithoutIsStrInference((s)[:16:])), default__.HexToU64(_dafny.SeqWithoutIsStrInference((s)[16::])))
        d_119___mcc_h0_ = source18_[0]
        d_120___mcc_h1_ = source18_[1]
        source19_ = d_119___mcc_h0_
        if source19_.is_None:
            source20_ = d_120___mcc_h1_
            if source20_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_121___mcc_h2_ = source20_.v
                return MiscTypes.Option_None()
        elif True:
            d_122___mcc_h4_ = source19_.v
            source21_ = d_120___mcc_h1_
            if source21_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_123___mcc_h6_ = source21_.v
                d_124_v2_ = d_123___mcc_h6_
                d_125_v1_ = d_122___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__64) * (d_125_v1_)) + (d_124_v2_))

    @staticmethod
    def HexToU256(s):
        source22_ = (default__.HexToU128(_dafny.SeqWithoutIsStrInference((s)[:32:])), default__.HexToU128(_dafny.SeqWithoutIsStrInference((s)[32::])))
        d_126___mcc_h0_ = source22_[0]
        d_127___mcc_h1_ = source22_[1]
        source23_ = d_126___mcc_h0_
        if source23_.is_None:
            source24_ = d_127___mcc_h1_
            if source24_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_128___mcc_h2_ = source24_.v
                return MiscTypes.Option_None()
        elif True:
            d_129___mcc_h4_ = source23_.v
            source25_ = d_127___mcc_h1_
            if source25_.is_None:
                return MiscTypes.Option_None()
            elif True:
                d_130___mcc_h6_ = source25_.v
                d_131_v2_ = d_130___mcc_h6_
                d_132_v1_ = d_129___mcc_h4_
                return MiscTypes.Option_Some(((Int.default__.TWO__128) * (d_132_v1_)) + (d_131_v2_))

    @staticmethod
    def U8ToHex(n):
        return (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_division(n, Int.default__.TWO__4))])) + (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_modulus(n, Int.default__.TWO__4))]))

    @staticmethod
    def HexHelper(s):
        d_133___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_133___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_133___accumulator_ = (d_133___accumulator_) + (default__.U8ToHex((s)[0]))
                    in12_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in12_
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
        d_134___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) < (16):
                    return (_dafny.SeqWithoutIsStrInference([default__.DecToHex(n)])) + (d_134___accumulator_)
                elif True:
                    d_134___accumulator_ = (_dafny.SeqWithoutIsStrInference([default__.DecToHex(_dafny.euclidian_modulus(n, 16))])) + (d_134___accumulator_)
                    in13_ = _dafny.euclidian_division(n, 16)
                    n = in13_
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

