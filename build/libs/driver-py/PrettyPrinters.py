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
import EVMToolTips
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
                    d_728_formattedAddress_: _dafny.Seq
                    d_728_formattedAddress_ = (Hex.default__.U32ToHex(((s)[0]).address) if (((s)[0]).address) < (Int.default__.TWO__32) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "OutofRange")))
                    _dafny.print((d_728_formattedAddress_).VerbatimString(False))
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
                    d_729_k_: int
                    d_729_k_ = ((xs)[0]).WeakestPreOperands(0)
                    d_730_l_: int
                    d_730_l_ = ((xs)[0]).WeakestPreCapacity(0)
                    if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMP/JUMPI: tgt address at the end: "))).VerbatimString(False))
                        d_731_r_: MiscTypes.Either
                        d_731_r_ = SegBuilder.default__.JUMPResolver((xs)[0])
                        source50_ = d_731_r_
                        if source50_.is_Left:
                            d_732___mcc_h0_ = source50_.l
                            d_733_v_ = d_732___mcc_h0_
                            source51_ = d_733_v_
                            if source51_.is_Value:
                                d_734___mcc_h2_ = source51_.v
                                d_735_address_ = d_734___mcc_h2_
                                _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex(d_735_address_))).VerbatimString(False))
                            elif True:
                                d_736___mcc_h3_ = source51_.s
                                d_737_msg_ = d_736___mcc_h3_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not determine stack value"))).VerbatimString(False))
                        elif True:
                            d_738___mcc_h1_ = source50_.r
                            d_739_stackPos_ = d_738___mcc_h1_
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Peek("))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_739_stackPos_))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if ((xs)[0]).is_CONTSeg:
                        if (((((xs)[0]).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_740_nextPC_: int
                            d_740_nextPC_ = ((xs)[0]).StartAddressNextSeg()
                            _dafny.print(((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: PC of instruction after last is: "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex(d_740_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        elif True:
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: has an invaid instructiom"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Operands:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_729_k_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Capacity:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_730_l_))
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
        d_741___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_741___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_741___accumulator_ = (d_741___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in75_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in75_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDestAsString(xs):
        d_742___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_742___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_742___accumulator_ = (d_742___accumulator_) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ensures s.IsJumpDest(0x"))) + (Hex.default__.NatToHex((xs)[0]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as u256)\n"))))
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
        d_743_j_: _dafny.Seq
        d_743_j_ = default__.CollectJumpDestAsString(default__.CollectJumpDest(xs))
        if (len(d_743_j_)) > (0):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/** Lemma for Jumpdest */"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((d_743_j_).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        default__.PrintProofObjectBody(xs, 0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def PrintProofObjectBody(xs, num):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_744_startAddress_: _dafny.Seq
                    d_744_startAddress_ = Hex.default__.NatToHex((((((xs)[0]).s).Ins())[0]).address)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Code starting at 0x"))).VerbatimString(False))
                    _dafny.print((d_744_startAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " */\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function {:opaque} ExecuteFromTag_"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(num))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EvmState.ExecutingState): (s': EvmState.State)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.PC() == 0x"))).VerbatimString(False))
                    _dafny.print((d_744_startAddress_).VerbatimString(False))
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
                            source52_ = ((xs)[0]).tgt
                            if source52_.is_Left:
                                d_745___mcc_h0_ = source52_.l
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))).VerbatimString(False))
                            elif True:
                                d_746___mcc_h2_ = source52_.r
                                d_747_v_ = d_746___mcc_h2_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.IsJumpDest(s0.Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_747_v_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "))\n"))).VerbatimString(False))
                    source53_ = (xs)[0]
                    if source53_.is_JUMP:
                        d_748___mcc_h4_ = source53_.s
                        d_749___mcc_h5_ = source53_.wpOp
                        d_750___mcc_h6_ = source53_.wpCap
                        d_751___mcc_h7_ = source53_.tgt
                        d_752___mcc_h8_ = source53_.stacks
                        d_753_tgt_ = d_751___mcc_h7_
                        d_754_s_ = d_748___mcc_h4_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() ==  "))).VerbatimString(False))
                        if True:
                            source54_ = d_753_tgt_
                            if source54_.is_Left:
                                d_755___mcc_h17_ = source54_.l
                                d_756_xc_ = d_755___mcc_h17_
                                source55_ = d_756_xc_
                                if source55_.is_Value:
                                    d_757___mcc_h19_ = source55_.v
                                    d_758_v_ = d_757___mcc_h19_
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))).VerbatimString(False))
                                    _dafny.print((Hex.default__.NatToHex((d_756_xc_).Extract())).VerbatimString(False))
                                elif True:
                                    d_759___mcc_h21_ = source55_.s
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not extract value "))).VerbatimString(False))
                            elif True:
                                d_760___mcc_h18_ = source54_.r
                                d_761_v_ = d_760___mcc_h18_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s0.Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_761_v_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ") as nat"))).VerbatimString(False))
                        if ((((d_754_s_).lastIns).op).opcode) == (EVMConstants.default__.JUMPI):
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " || s'.PC() == 0x"))).VerbatimString(False))
                            _dafny.print((Hex.default__.NatToHex((((d_754_s_).lastIns).address) + (1))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        d_762_n_: int
                        d_762_n_ = ((xs)[0]).StackEffect()
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                        if (d_762_n_) >= (0):
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_762_n_))
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of((0) - (d_762_n_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif source53_.is_CONT:
                        d_763___mcc_h9_ = source53_.s
                        d_764___mcc_h10_ = source53_.wpOp
                        d_765___mcc_h11_ = source53_.wpCap
                        d_766___mcc_h12_ = source53_.stacks
                        d_767_s_ = d_763___mcc_h9_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                        if ((((d_767_s_).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_768_nextPC_: int
                            d_768_nextPC_ = (d_767_s_).StartAddressNextSeg()
                            _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() == 0x"))) + (Hex.default__.NatToHex(d_768_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                            d_769_n_: int
                            d_769_n_ = ((xs)[0]).StackEffect()
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                            if (d_769_n_) >= (0):
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_769_n_))
                            elif True:
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                                _dafny.print(_dafny.string_of((0) - (d_769_n_)))
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  Last instruction is invalid"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif True:
                        d_770___mcc_h13_ = source53_.s
                        d_771___mcc_h14_ = source53_.wpOp
                        d_772___mcc_h15_ = source53_.wpCap
                        d_773___mcc_h16_ = source53_.stacks
                        d_774_s_ = d_770___mcc_h13_
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
                    d_775_k_: _dafny.Seq
                    d_775_k_ = PrettyIns.default__.PrintInstructionToDafny((xs)[0], pos, (pos) + (1))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((d_775_k_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in79_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in80_ = (pos) + (1)
                    xs = in79_
                    pos = in80_
                    raise _dafny.TailCall()
                break

