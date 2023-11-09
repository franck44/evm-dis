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
                    source33_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[:2:]))
                    if source33_.is_None:
                        return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference((s)[:2:]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "' is not a known opcode"))), next)]))
                    elif True:
                        d_447___mcc_h0_ = source33_.v
                        d_448_v_ = d_447___mcc_h0_
                        d_449_op_ = OpcodeDecoder.default__.Decode(d_448_v_)
                        if ((d_449_op_).Args()) > (0):
                            if ((len(_dafny.SeqWithoutIsStrInference((s)[2::]))) < ((2) * ((d_449_op_).Args()))) or (not(default__.IsHexString(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_449_op_).Args()):])))):
                                return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "not enough arguments for "))) + (_dafny.SeqWithoutIsStrInference((s)[2::])), next)]))
                            elif True:
                                in11_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[(2) * ((d_449_op_).Args())::])
                                in12_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_449_op_, _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[2::]))[:(2) * ((d_449_op_).Args()):]), next)]))
                                in13_ = ((next) + (1)) + ((d_449_op_).Args())
                                s = in11_
                                p = in12_
                                next = in13_
                                raise _dafny.TailCall()
                        elif True:
                            in14_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                            in15_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_449_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                            in16_ = (next) + (1)
                            s = in14_
                            p = in15_
                            next = in16_
                            raise _dafny.TailCall()
                break

    @staticmethod
    def IsHexString(s):
        def lambda17_(forall_var_3_):
            d_450_k_: int = forall_var_3_
            return not (((0) <= (d_450_k_)) and ((d_450_k_) < (len(s)))) or (Hex.default__.IsHex((s)[d_450_k_]))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda17_)

    @staticmethod
    def DisassembleU8(s, p, next):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return p
                elif True:
                    d_451_op_ = OpcodeDecoder.default__.Decode((s)[0])
                    if ((d_451_op_).Args()) > (0):
                        if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < ((d_451_op_).Args()):
                            return (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(OpcodeDecoder.default__.Decode(EVMConstants.default__.INVALID), _dafny.SeqWithoutIsStrInference([]), 0)]))
                        elif True:
                            in17_ = _dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[(d_451_op_).Args()::])
                            in18_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_451_op_, default__.HexHelper(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:(d_451_op_).Args():])), next)]))
                            in19_ = ((next) + (1)) + ((d_451_op_).Args())
                            s = in17_
                            p = in18_
                            next = in19_
                            raise _dafny.TailCall()
                    elif True:
                        in20_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        in21_ = (p) + (_dafny.SeqWithoutIsStrInference([Instructions.Instruction_Instruction(d_451_op_, _dafny.SeqWithoutIsStrInference([]), next)]))
                        in22_ = (next) + (1)
                        s = in20_
                        p = in21_
                        next = in22_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def HexHelper(s):
        d_452___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_452___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_452___accumulator_ = (d_452___accumulator_) + (Hex.default__.U8ToHex((s)[0]))
                    in23_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in23_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def StringToU8Helper(s, decoded):
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return MiscTypes.Option_Some(decoded)
                elif (len(s)) == (1):
                    source34_ = Hex.default__.HexToU8((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0"))) + (_dafny.SeqWithoutIsStrInference([(s)[0]])))
                    if source34_.is_None:
                        return MiscTypes.Option_None()
                    elif True:
                        d_453___mcc_h0_ = source34_.v
                        d_454_v_ = d_453___mcc_h0_
                        return MiscTypes.Option_Some((decoded) + (_dafny.SeqWithoutIsStrInference([d_454_v_])))
                elif True:
                    source35_ = Hex.default__.HexToU8(_dafny.SeqWithoutIsStrInference((s)[0:2:]))
                    if source35_.is_None:
                        return MiscTypes.Option_None()
                    elif True:
                        d_455___mcc_h1_ = source35_.v
                        d_456_v_ = d_455___mcc_h1_
                        in24_ = _dafny.SeqWithoutIsStrInference((s)[2::])
                        in25_ = (decoded) + (_dafny.SeqWithoutIsStrInference([d_456_v_]))
                        s = in24_
                        decoded = in25_
                        raise _dafny.TailCall()
                break

