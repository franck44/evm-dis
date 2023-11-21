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
                    d_587_formattedAddress_: _dafny.Seq
                    d_587_formattedAddress_ = (Hex.default__.U32ToHex(((s)[0]).address) if (((s)[0]).address) < (Int.default__.TWO__32) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "OutofRange")))
                    _dafny.print((d_587_formattedAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": "))).VerbatimString(False))
                    _dafny.print((((s)[0]).ToString()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in72_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in72_
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
                    d_588_k_: int
                    d_588_k_ = ((xs)[0]).WeakestPreOperands(0)
                    d_589_l_: int
                    d_589_l_ = ((xs)[0]).WeakestPreCapacity(0)
                    if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMP/JUMPI: tgt address at the end: "))).VerbatimString(False))
                        d_590_r_: MiscTypes.Either
                        d_590_r_ = SegBuilder.default__.JUMPResolver((xs)[0])
                        source49_ = d_590_r_
                        if source49_.is_Left:
                            d_591___mcc_h0_ = source49_.l
                            d_592_v_ = d_591___mcc_h0_
                            source50_ = d_592_v_
                            if source50_.is_Value:
                                d_593___mcc_h2_ = source50_.v
                                d_594_address_ = d_593___mcc_h2_
                                _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex(d_594_address_))).VerbatimString(False))
                            elif True:
                                d_595___mcc_h3_ = source50_.s
                                d_596_msg_ = d_595___mcc_h3_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not determine stack value"))).VerbatimString(False))
                        elif True:
                            d_597___mcc_h1_ = source49_.r
                            d_598_stackPos_ = d_597___mcc_h1_
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Peek("))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_598_stackPos_))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if ((xs)[0]).is_CONTSeg:
                        if (((((xs)[0]).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_599_nextPC_: int
                            d_599_nextPC_ = ((xs)[0]).StartAddressNextSeg()
                            _dafny.print(((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: PC of instruction after last is: "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex(d_599_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        elif True:
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: has an invaid instructiom"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Operands:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_588_k_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Capacity:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_589_l_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Net Stack Effect:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(((xs)[0]).StackEffect()))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    default__.PrintInstructions(((xs)[0]).Ins())
                    in73_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in74_ = (num) + (1)
                    xs = in73_
                    num = in74_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDest(xs):
        d_600___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_600___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_600___accumulator_ = (d_600___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in75_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in75_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDestAsString(xs):
        d_601___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_601___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_601___accumulator_ = (d_601___accumulator_) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ensures s.IsJumpDest(0x"))) + (Hex.default__.NatToHex((xs)[0]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as u256)\n"))))
                    in76_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in76_
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
        d_602_j_: _dafny.Seq
        d_602_j_ = default__.CollectJumpDestAsString(default__.CollectJumpDest(xs))
        if (len(d_602_j_)) > (0):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/** Lemma for Jumpdest */"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((d_602_j_).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        default__.PrintProofObjectBody(xs, 0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def PrintProofObjectBody(xs, num):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_603_startAddress_: _dafny.Seq
                    d_603_startAddress_ = Hex.default__.NatToHex((((((xs)[0]).s).Ins())[0]).address)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Code starting at 0x"))).VerbatimString(False))
                    _dafny.print((d_603_startAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " */\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function {:opaque} ExecuteFromTag_"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(num))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EvmState.ExecutingState): (s': EvmState.State)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.PC() == 0x"))).VerbatimString(False))
                    _dafny.print((d_603_startAddress_).VerbatimString(False))
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
                            source51_ = ((xs)[0]).tgt
                            if source51_.is_Left:
                                d_604___mcc_h0_ = source51_.l
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))).VerbatimString(False))
                            elif True:
                                d_605___mcc_h2_ = source51_.r
                                d_606_v_ = d_605___mcc_h2_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.IsJumpDest(s0.Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_606_v_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "))\n"))).VerbatimString(False))
                    source52_ = (xs)[0]
                    if source52_.is_JUMP:
                        d_607___mcc_h4_ = source52_.s
                        d_608___mcc_h5_ = source52_.wpOp
                        d_609___mcc_h6_ = source52_.wpCap
                        d_610___mcc_h7_ = source52_.tgt
                        d_611___mcc_h8_ = source52_.stacks
                        d_612_tgt_ = d_610___mcc_h7_
                        d_613_s_ = d_607___mcc_h4_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() ==  "))).VerbatimString(False))
                        if True:
                            source53_ = d_612_tgt_
                            if source53_.is_Left:
                                d_614___mcc_h17_ = source53_.l
                                d_615_xc_ = d_614___mcc_h17_
                                source54_ = d_615_xc_
                                if source54_.is_Value:
                                    d_616___mcc_h19_ = source54_.v
                                    d_617_v_ = d_616___mcc_h19_
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))).VerbatimString(False))
                                    _dafny.print((Hex.default__.NatToHex((d_615_xc_).Extract())).VerbatimString(False))
                                elif True:
                                    d_618___mcc_h21_ = source54_.s
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not extract value "))).VerbatimString(False))
                            elif True:
                                d_619___mcc_h18_ = source53_.r
                                d_620_v_ = d_619___mcc_h18_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s0.Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_620_v_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ") as nat"))).VerbatimString(False))
                        if ((((d_613_s_).lastIns).op).opcode) == (EVMConstants.default__.JUMPI):
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " || s'.PC() == 0x"))).VerbatimString(False))
                            _dafny.print((Hex.default__.NatToHex((((d_613_s_).lastIns).address) + (1))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        d_621_n_: int
                        d_621_n_ = ((xs)[0]).StackEffect()
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                        if (d_621_n_) >= (0):
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_621_n_))
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of((0) - (d_621_n_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif source52_.is_CONT:
                        d_622___mcc_h9_ = source52_.s
                        d_623___mcc_h10_ = source52_.wpOp
                        d_624___mcc_h11_ = source52_.wpCap
                        d_625___mcc_h12_ = source52_.stacks
                        d_626_s_ = d_622___mcc_h9_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                        if ((((d_626_s_).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_627_nextPC_: int
                            d_627_nextPC_ = (d_626_s_).StartAddressNextSeg()
                            _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() == 0x"))) + (Hex.default__.NatToHex(d_627_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                            d_628_n_: int
                            d_628_n_ = ((xs)[0]).StackEffect()
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                            if (d_628_n_) >= (0):
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_628_n_))
                            elif True:
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                                _dafny.print(_dafny.string_of((0) - (d_628_n_)))
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  Last instruction is invalid"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif True:
                        d_629___mcc_h13_ = source52_.s
                        d_630___mcc_h14_ = source52_.wpOp
                        d_631___mcc_h15_ = source52_.wpCap
                        d_632___mcc_h16_ = source52_.stacks
                        d_633_s_ = d_629___mcc_h13_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.RETURNS?\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "{\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ValidJumpDest(s0);\n"))).VerbatimString(False))
                    default__.PrintInstructionsToDafny((((xs)[0]).s).Ins(), 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  s"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((((xs)[0]).s).Ins())))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))
                    in77_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in78_ = (num) + (1)
                    xs = in77_
                    num = in78_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintInstructionsToDafny(xs, pos):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_634_k_: _dafny.Seq
                    d_634_k_ = PrettyIns.default__.PrintInstructionToDafny((xs)[0], pos, (pos) + (1))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((d_634_k_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in79_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in80_ = (pos) + (1)
                    xs = in79_
                    pos = in80_
                    raise _dafny.TailCall()
                break

