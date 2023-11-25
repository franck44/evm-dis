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
import WeakPre
import State
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
                        d_530___mcc_h0_ = source40_.v
                        d_531_v_ = d_530___mcc_h0_
                        d_532_op_ = OpcodeDecoder.default__.Decode(d_531_v_)
                        if ((d_532_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_532_op_).Args()))) or (not(default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_532_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for "))) + (_dafny.SeqWithoutIsStrInference((s)[2::])), next)]))
                            elif True:
                                in25_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_532_op_).Args())::])
                                in26_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_532_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_532_op_).Args()):]), next)]))
                                in27_ = ((next) + (1)) + ((d_532_op_).Args())
                                s = in25_
                                p = in26_
                                next = in27_
                                raise _dafny.TailCall()
                        elif True:
                            in28_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in29_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_532_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in30_ = (next) + (1)
                            s = in28_
                            p = in29_
                            next = in30_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def IsHexString(s):
        def lambda32_(forall_var_3_):
            d_533_k_: int = forall_var_3_
            return not (((0) <= (d_533_k_)) and ((d_533_k_) < (len(s)))) or (Hex.default__.IsHex((s)[d_533_k_]))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda32_)

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_534_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_534_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_534_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), 0)]))
                        elif True:
                            in31_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_534_op_).Args()::])
                            in32_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_534_op_, default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_534_op_).Args():])), next)]))
                            in33_ = ((next) + (1)) + ((d_534_op_).Args())
                            s = in31_
                            p = in32_
                            next = in33_
                            raise _dafny.TailCall()
                    elif True:
                        in34_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in35_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_534_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in36_ = (next) + (1)
                        s = in34_
                        p = in35_
                        next = in36_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def HexHelper(s):
        d_535___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_535___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_535___accumulator_ = (d_535___accumulator_) + (Hex.default__.U8ToHex((s)[0]))
                    in37_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in37_
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
                        d_536___mcc_h0_ = source41_.v
                        d_537_v_ = d_536___mcc_h0_
                        return MiscTypes.Option_Some((decoded) + (_dafny.SeqWithoutIsStrInference([d_537_v_])))
                elif True:
                    source42_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[0:2:]))
                    if source42_.is_None:
                        return MiscTypes.Option_None()
                    elif True:
                        d_538___mcc_h1_ = source42_.v
                        d_539_v_ = d_538___mcc_h1_
                        in38_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                        in39_ = (decoded) + (_dafny.SeqWithoutIsStrInference([d_539_v_]))
                        s = in38_
                        decoded = in39_
                        raise _dafny.TailCall()
                break

