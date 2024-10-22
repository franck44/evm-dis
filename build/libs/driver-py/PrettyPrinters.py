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
import Hex as Hex
import StackElement as StackElement
import WeakPre as WeakPre
import State as State
import EVMToolTips as EVMToolTips
import Instructions as Instructions
import BinaryDecoder as BinaryDecoder
import LinSegments as LinSegments
import Splitter as Splitter
import SegBuilder as SegBuilder
import CFGState as CFGState
import ProofObject as ProofObject
import PrettyIns as PrettyIns

# Module: PrettyPrinters

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def PrintInstructions(s):
        while True:
            with _dafny.label():
                if (len(s)) > (0):
                    d_0_formattedAddress_: _dafny.Seq
                    if (((s)[0]).address) < (Int.default__.TWO__32):
                        d_0_formattedAddress_ = Hex.default__.U32ToHex(((s)[0]).address)
                    elif True:
                        d_0_formattedAddress_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "OutofRange"))
                    _dafny.print((d_0_formattedAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": "))).VerbatimString(False))
                    _dafny.print((((s)[0]).ToString()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in0_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintSegments(xs, num):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------------------------------------\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(num))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_0_k_: int
                    d_0_k_ = ((xs)[0]).WeakestPreOperands(((xs)[0]).Ins(), 0)
                    d_1_l_: int
                    d_1_l_ = ((xs)[0]).WeakestPreCapacity(0)
                    if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMP/JUMPI: tgt address at the end: "))).VerbatimString(False))
                        d_2_r_: MiscTypes.Either
                        d_2_r_ = SegBuilder.default__.JUMPResolver((xs)[0])
                        source0_ = d_2_r_
                        with _dafny.label("match0"):
                            if True:
                                if source0_.is_Left:
                                    d_3_v_ = source0_.l
                                    source1_ = d_3_v_
                                    with _dafny.label("match1"):
                                        if True:
                                            if source1_.is_Value:
                                                d_4_address_ = source1_.v
                                                _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex(d_4_address_))).VerbatimString(False))
                                                raise _dafny.Break("match1")
                                        if True:
                                            d_5_msg_ = source1_.s
                                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not determine stack value"))).VerbatimString(False))
                                        pass
                                    raise _dafny.Break("match0")
                            if True:
                                d_6_stackPos_ = source0_.r
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_6_stackPos_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")"))).VerbatimString(False))
                            pass
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if ((xs)[0]).is_CONTSeg:
                        if (((((xs)[0]).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_7_nextPC_: int
                            d_7_nextPC_ = ((xs)[0]).StartAddressNextSeg()
                            _dafny.print(((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: PC of instruction after last is: "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex(d_7_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        elif True:
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: has an invalid instruction"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Operands:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_0_k_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Capacity:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_1_l_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Net Stack Effect:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(((xs)[0]).StackEffect()))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    default__.PrintInstructions(((xs)[0]).Ins())
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in1_ = (num) + (1)
                    xs = in0_
                    num = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDest(xs):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDestAsString(xs):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ensures s.IsJumpDest(0x"))) + (Hex.default__.NatToHex((xs)[0]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as u256)\n"))))
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintProofObjectToDafny(xs, pathToEVMDafny):
        if (len(pathToEVMDafny)) > (0):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "include \""))).VerbatimString(False))
            _dafny.print((pathToEVMDafny).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/src/dafny/state.dfy\""))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "include \""))).VerbatimString(False))
            _dafny.print((pathToEVMDafny).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/src/dafny/bytecode.dfy\""))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "module DafnyEVMProofObject {"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened Int"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import EvmState"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "import opened Bytecode"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        d_0_j_: _dafny.Seq
        d_0_j_ = default__.CollectJumpDestAsString(default__.CollectJumpDest(xs))
        if (len(d_0_j_)) > (0):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/** Lemma for Jumpdest */"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((d_0_j_).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        default__.PrintProofObjectBody(xs, 0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def PrintProofObjectBody(xs, num):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_0_startAddress_: _dafny.Seq
                    d_0_startAddress_ = Hex.default__.NatToHex((((((xs)[0]).s).Ins())[0]).address)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Code starting at 0x"))).VerbatimString(False))
                    _dafny.print((d_0_startAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " */\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function {:opaque} ExecuteFromTag_"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(num))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EvmState.ExecutingState): (s': EvmState.State)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.PC() == 0x"))).VerbatimString(False))
                    _dafny.print((d_0_startAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as nat\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Net Operands effect "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((((xs)[0]).s).NetOpEffect()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.Operands() >= "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(((xs)[0]).wpOp))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  // Net Capacity effect "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((((xs)[0]).s).NetCapEffect()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.Capacity() >= "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(((xs)[0]).wpCap))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if (((xs)[0]).is_JUMP) and ((((((xs)[0]).s).lastIns).op).IsJump()):
                        if True:
                            source0_ = ((xs)[0]).tgt
                            with _dafny.label("match0"):
                                if True:
                                    if source0_.is_Right:
                                        d_1_v_ = source0_.r
                                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.IsJumpDest(s0.Peek("))).VerbatimString(False))
                                        _dafny.print(_dafny.string_of(d_1_v_))
                                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "))\n"))).VerbatimString(False))
                                        raise _dafny.Break("match0")
                                if True:
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))).VerbatimString(False))
                                pass
                    source1_ = (xs)[0]
                    with _dafny.label("match1"):
                        if True:
                            if source1_.is_JUMP:
                                d_2_s_ = source1_.s
                                d_3_tgt_ = source1_.tgt
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() ==  "))).VerbatimString(False))
                                if True:
                                    source2_ = d_3_tgt_
                                    with _dafny.label("match2"):
                                        if True:
                                            if source2_.is_Left:
                                                d_4_xc_ = source2_.l
                                                source3_ = d_4_xc_
                                                with _dafny.label("match3"):
                                                    if True:
                                                        if source3_.is_Value:
                                                            d_5_v_ = source3_.v
                                                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))).VerbatimString(False))
                                                            _dafny.print((Hex.default__.NatToHex((d_4_xc_).Extract())).VerbatimString(False))
                                                            raise _dafny.Break("match3")
                                                    if True:
                                                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not extract value "))).VerbatimString(False))
                                                    pass
                                                raise _dafny.Break("match2")
                                        if True:
                                            d_6_v_ = source2_.r
                                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s0.Peek("))).VerbatimString(False))
                                            _dafny.print(_dafny.string_of(d_6_v_))
                                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ") as nat"))).VerbatimString(False))
                                        pass
                                if ((((d_2_s_).lastIns).op).opcode) == (EVMConstants.default__.JUMPI):
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " || s'.PC() == 0x"))).VerbatimString(False))
                                    _dafny.print((Hex.default__.NatToHex((((d_2_s_).lastIns).address) + (1))).VerbatimString(False))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                                d_7_n_: int
                                d_7_n_ = ((xs)[0]).StackEffect()
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                                if (d_7_n_) >= (0):
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                                    _dafny.print(_dafny.string_of(d_7_n_))
                                elif True:
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                                    _dafny.print(_dafny.string_of((0) - (d_7_n_)))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                                raise _dafny.Break("match1")
                        if True:
                            if source1_.is_CONT:
                                d_8_s_ = source1_.s
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                                if ((((d_8_s_).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                                    d_9_nextPC_: int
                                    d_9_nextPC_ = (d_8_s_).StartAddressNextSeg()
                                    _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() == 0x"))) + (Hex.default__.NatToHex(d_9_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                                    d_10_n_: int
                                    d_10_n_ = ((xs)[0]).StackEffect()
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                                    if (d_10_n_) >= (0):
                                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                                        _dafny.print(_dafny.string_of(d_10_n_))
                                    elif True:
                                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                                        _dafny.print(_dafny.string_of((0) - (d_10_n_)))
                                elif True:
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  Last instruction is invalid"))).VerbatimString(False))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                                raise _dafny.Break("match1")
                        if True:
                            d_11_s_ = source1_.s
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.RETURNS?\n"))).VerbatimString(False))
                        pass
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "{\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ValidJumpDest(s0);\n"))).VerbatimString(False))
                    default__.PrintInstructionsToDafny((((xs)[0]).s).Ins(), 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  s"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((((xs)[0]).s).Ins())))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in1_ = (num) + (1)
                    xs = in0_
                    num = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintInstructionsToDafny(xs, pos):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_0_k_: _dafny.Seq
                    d_0_k_ = PrettyIns.default__.PrintInstructionToDafny((xs)[0], pos, (pos) + (1))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((d_0_k_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in1_ = (pos) + (1)
                    xs = in0_
                    pos = in1_
                    raise _dafny.TailCall()
                break

