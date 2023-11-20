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
                    source40_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source40_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference((s)[:2:]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "' is not a known opcode"))), next)]))
                    elif True:
                        d_475___mcc_h0_ = source40_.v
                        d_476_v_ = d_475___mcc_h0_
                        d_477_op_ = OpcodeDecoder.default__.Decode(d_476_v_)
                        if ((d_477_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_477_op_).Args()))) or (not(default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_477_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for "))) + (_dafny.SeqWithoutIsStrInference((s)[2::])), next)]))
                            elif True:
                                in19_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_477_op_).Args())::])
                                in20_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_477_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_477_op_).Args()):]), next)]))
                                in21_ = ((next) + (1)) + ((d_477_op_).Args())
                                s = in19_
                                p = in20_
                                next = in21_
                                raise _dafny.TailCall()
                        elif True:
                            in22_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in23_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_477_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in24_ = (next) + (1)
                            s = in22_
                            p = in23_
                            next = in24_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def IsHexString(s):
        def lambda17_(forall_var_3_):
            d_478_k_: int = forall_var_3_
            return not (((0) <= (d_478_k_)) and ((d_478_k_) < (len(s)))) or (Hex.default__.IsHex((s)[d_478_k_]))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda17_)

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_479_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_479_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_479_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), 0)]))
                        elif True:
                            in25_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_479_op_).Args()::])
                            in26_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_479_op_, default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_479_op_).Args():])), next)]))
                            in27_ = ((next) + (1)) + ((d_479_op_).Args())
                            s = in25_
                            p = in26_
                            next = in27_
                            raise _dafny.TailCall()
                    elif True:
                        in28_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in29_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_479_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in30_ = (next) + (1)
                        s = in28_
                        p = in29_
                        next = in30_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def HexHelper(s):
        d_480___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_480___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_480___accumulator_ = (d_480___accumulator_) + (Hex.default__.U8ToHex((s)[0]))
                    in31_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in31_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def StringToU8Helper(s, decoded):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return MiscTypes.Option_Some(decoded)
                elif (len(s)) == (1):
                    source41_ = Hex.default__.HexToU8((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0"))) + (_dafny.SeqWithoutIsStrInference([(s)[0]])))
                    if source41_.is_None:
                        return MiscTypes.Option_None()
                    elif True:
                        d_481___mcc_h0_ = source41_.v
                        d_482_v_ = d_481___mcc_h0_
                        return MiscTypes.Option_Some((decoded) + (_dafny.SeqWithoutIsStrInference([d_482_v_])))
                elif True:
                    source42_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[0:2:]))
                    if source42_.is_None:
                        return MiscTypes.Option_None()
                    elif True:
                        d_483___mcc_h1_ = source42_.v
                        d_484_v_ = d_483___mcc_h1_
                        in32_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                        in33_ = (decoded) + (_dafny.SeqWithoutIsStrInference([d_484_v_]))
                        s = in32_
                        decoded = in33_
                        raise _dafny.TailCall()
                break

