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
import BinaryDecoder
import LinSegments
import Splitter
import SegBuilder
import ProofObject
import PrettyIns

# Module: PrettyPrinters

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def PrintInstructions(s):
        while True:
            with _dafny.label():
                if (len(s)) > (0):
                    d_520_formattedAddress_: _dafny.Seq
                    d_520_formattedAddress_ = (Hex.default__.U32ToHex(((s)[0]).address) if (((s)[0]).address) < (Int.default__.TWO__32) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "OutofRange")))
                    _dafny.print((d_520_formattedAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": "))).VerbatimString(False))
                    _dafny.print((((s)[0]).ToString()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in50_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in50_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintSegments(xs, num):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(num))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_521_k_: int
                    d_521_k_ = ((xs)[0]).WeakestPreOperands(0)
                    d_522_l_: int
                    d_522_l_ = ((xs)[0]).WeakestPreCapacity(0)
                    if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMP/JUMPI: tgt address at the end: "))).VerbatimString(False))
                        d_523_r_: MiscTypes.Either
                        d_523_r_ = SegBuilder.default__.JUMPResolver((xs)[0])
                        source41_ = d_523_r_
                        if source41_.is_Left:
                            d_524___mcc_h0_ = source41_.l
                            d_525_v_ = d_524___mcc_h0_
                            source42_ = d_525_v_
                            if source42_.is_Value:
                                d_526___mcc_h2_ = source42_.v
                                d_527_address_ = d_526___mcc_h2_
                                _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex(d_527_address_))).VerbatimString(False))
                            elif True:
                                d_528___mcc_h3_ = source42_.s
                                d_529_msg_ = d_528___mcc_h3_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not determine stack value"))).VerbatimString(False))
                        elif True:
                            d_530___mcc_h1_ = source41_.r
                            d_531_stackPos_ = d_530___mcc_h1_
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Peek("))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_531_stackPos_))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if ((xs)[0]).is_CONTSeg:
                        if (((((xs)[0]).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_532_nextPC_: int
                            d_532_nextPC_ = ((xs)[0]).StartAddressNextSeg()
                            _dafny.print(((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: PC of instruction after last is: "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex(d_532_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        elif True:
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: has an invaid instructiom"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Operands:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_521_k_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Capacity:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_522_l_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Net Stack Effect:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(((xs)[0]).StackEffect()))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    default__.PrintInstructions(((xs)[0]).Ins())
                    in51_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in52_ = (num) + (1)
                    xs = in51_
                    num = in52_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDest(xs):
        d_533___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_533___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_533___accumulator_ = (d_533___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in53_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in53_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDestAsString(xs):
        d_534___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_534___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_534___accumulator_ = (d_534___accumulator_) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ensures s.IsJumpDest(0x"))) + (Hex.default__.NatToHex((xs)[0]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as u256)\n"))))
                    in54_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in54_
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
        d_535_j_: _dafny.Seq
        d_535_j_ = default__.CollectJumpDestAsString(default__.CollectJumpDest(xs))
        if (len(d_535_j_)) > (0):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/** Lemma for Jumpdest */"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((d_535_j_).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        default__.PrintProofObjectBody(xs, 0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def PrintProofObjectBody(xs, num):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_536_startAddress_: _dafny.Seq
                    d_536_startAddress_ = Hex.default__.NatToHex((((((xs)[0]).s).Ins())[0]).address)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Code starting at 0x"))).VerbatimString(False))
                    _dafny.print((d_536_startAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " */\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function {:opaque} ExecuteFromTag_"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(num))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EvmState.ExecutingState): (s': EvmState.State)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.PC() == 0x"))).VerbatimString(False))
                    _dafny.print((d_536_startAddress_).VerbatimString(False))
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
                            source43_ = ((xs)[0]).tgt
                            if source43_.is_Left:
                                d_537___mcc_h0_ = source43_.l
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))).VerbatimString(False))
                            elif True:
                                d_538___mcc_h2_ = source43_.r
                                d_539_v_ = d_538___mcc_h2_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.IsJumpDest(s0.Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_539_v_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "))\n"))).VerbatimString(False))
                    source44_ = (xs)[0]
                    if source44_.is_JUMP:
                        d_540___mcc_h4_ = source44_.s
                        d_541___mcc_h5_ = source44_.wpOp
                        d_542___mcc_h6_ = source44_.wpCap
                        d_543___mcc_h7_ = source44_.tgt
                        d_544___mcc_h8_ = source44_.stacks
                        d_545_tgt_ = d_543___mcc_h7_
                        d_546_s_ = d_540___mcc_h4_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() ==  "))).VerbatimString(False))
                        if True:
                            source45_ = d_545_tgt_
                            if source45_.is_Left:
                                d_547___mcc_h17_ = source45_.l
                                d_548_xc_ = d_547___mcc_h17_
                                source46_ = d_548_xc_
                                if source46_.is_Value:
                                    d_549___mcc_h19_ = source46_.v
                                    d_550_v_ = d_549___mcc_h19_
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))).VerbatimString(False))
                                    _dafny.print((Hex.default__.NatToHex((d_548_xc_).Extract())).VerbatimString(False))
                                elif True:
                                    d_551___mcc_h21_ = source46_.s
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not extract value "))).VerbatimString(False))
                            elif True:
                                d_552___mcc_h18_ = source45_.r
                                d_553_v_ = d_552___mcc_h18_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s0.Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_553_v_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ") as nat"))).VerbatimString(False))
                        if ((((d_546_s_).lastIns).op).opcode) == (EVMConstants.default__.JUMPI):
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " || s'.PC() == 0x"))).VerbatimString(False))
                            _dafny.print((Hex.default__.NatToHex((((d_546_s_).lastIns).address) + (1))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        d_554_n_: int
                        d_554_n_ = ((xs)[0]).StackEffect()
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                        if (d_554_n_) >= (0):
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_554_n_))
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of((0) - (d_554_n_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif source44_.is_CONT:
                        d_555___mcc_h9_ = source44_.s
                        d_556___mcc_h10_ = source44_.wpOp
                        d_557___mcc_h11_ = source44_.wpCap
                        d_558___mcc_h12_ = source44_.stacks
                        d_559_s_ = d_555___mcc_h9_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                        if ((((d_559_s_).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_560_nextPC_: int
                            d_560_nextPC_ = (d_559_s_).StartAddressNextSeg()
                            _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() == 0x"))) + (Hex.default__.NatToHex(d_560_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                            d_561_n_: int
                            d_561_n_ = ((xs)[0]).StackEffect()
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                            if (d_561_n_) >= (0):
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_561_n_))
                            elif True:
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                                _dafny.print(_dafny.string_of((0) - (d_561_n_)))
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  Last instruction is invalid"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif True:
                        d_562___mcc_h13_ = source44_.s
                        d_563___mcc_h14_ = source44_.wpOp
                        d_564___mcc_h15_ = source44_.wpCap
                        d_565___mcc_h16_ = source44_.stacks
                        d_566_s_ = d_562___mcc_h13_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.RETURNS?\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "{\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ValidJumpDest(s0);\n"))).VerbatimString(False))
                    default__.PrintInstructionsToDafny((((xs)[0]).s).Ins(), 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  s"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((((xs)[0]).s).Ins())))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))
                    in55_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in56_ = (num) + (1)
                    xs = in55_
                    num = in56_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintInstructionsToDafny(xs, pos):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_567_k_: _dafny.Seq
                    d_567_k_ = PrettyIns.default__.PrintInstructionToDafny((xs)[0], pos, (pos) + (1))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((d_567_k_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in57_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in58_ = (pos) + (1)
                    xs = in57_
                    pos = in58_
                    raise _dafny.TailCall()
                break

