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
import State
import WeakPre
import Instructions

# Module: BinaryDecoder

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Disassemble(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif (len(s)) == (1):
                    return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), s, next)]))
                elif True:
                    source35_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source35_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference((s)[:2:]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "' is not a known opcode"))), next)]))
                    elif True:
                        d_457___mcc_h0_ = source35_.v
                        d_458_v_ = d_457___mcc_h0_
                        d_459_op_ = OpcodeDecoder.default__.Decode(d_458_v_)
                        if ((d_459_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_459_op_).Args()))) or (not(default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_459_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for "))) + (_dafny.SeqWithoutIsStrInference((s)[2::])), next)]))
                            elif True:
                                in12_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_459_op_).Args())::])
                                in13_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_459_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_459_op_).Args()):]), next)]))
                                in14_ = ((next) + (1)) + ((d_459_op_).Args())
                                s = in12_
                                p = in13_
                                next = in14_
                                raise _dafny.TailCall()
                        elif True:
                            in15_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in16_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_459_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in17_ = (next) + (1)
                            s = in15_
                            p = in16_
                            next = in17_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def IsHexString(s):
        def lambda17_(forall_var_3_):
            d_460_k_: int = forall_var_3_
            return not (((0) <= (d_460_k_)) and ((d_460_k_) < (len(s)))) or (Hex.default__.IsHex((s)[d_460_k_]))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda17_)

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_461_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_461_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_461_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), 0)]))
                        elif True:
                            in18_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_461_op_).Args()::])
                            in19_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_461_op_, default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_461_op_).Args():])), next)]))
                            in20_ = ((next) + (1)) + ((d_461_op_).Args())
                            s = in18_
                            p = in19_
                            next = in20_
                            raise _dafny.TailCall()
                    elif True:
                        in21_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in22_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_461_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in23_ = (next) + (1)
                        s = in21_
                        p = in22_
                        next = in23_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def HexHelper(s):
        d_462___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_462___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_462___accumulator_ = (d_462___accumulator_) + (Hex.default__.U8ToHex((s)[0]))
                    in24_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in24_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def StringToU8Helper(s, decoded):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return MiscTypes.Option_Some(decoded)
                elif (len(s)) == (1):
                    source36_ = Hex.default__.HexToU8((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0"))) + (_dafny.SeqWithoutIsStrInference([(s)[0]])))
                    if source36_.is_None:
                        return MiscTypes.Option_None()
                    elif True:
                        d_463___mcc_h0_ = source36_.v
                        d_464_v_ = d_463___mcc_h0_
                        return MiscTypes.Option_Some((decoded) + (_dafny.SeqWithoutIsStrInference([d_464_v_])))
                elif True:
                    source37_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[0:2:]))
                    if source37_.is_None:
                        return MiscTypes.Option_None()
                    elif True:
                        d_465___mcc_h1_ = source37_.v
                        d_466_v_ = d_465___mcc_h1_
                        in25_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                        in26_ = (decoded) + (_dafny.SeqWithoutIsStrInference([d_466_v_]))
                        s = in25_
                        decoded = in26_
                        raise _dafny.TailCall()
                break

