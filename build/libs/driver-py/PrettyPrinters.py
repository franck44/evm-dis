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
                    d_712_formattedAddress_: _dafny.Seq
                    d_712_formattedAddress_ = (Hex.default__.U32ToHex(((s)[0]).address) if (((s)[0]).address) < (Int.default__.TWO__32) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "OutofRange")))
                    _dafny.print((d_712_formattedAddress_).VerbatimString(False))
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
                    d_713_k_: int
                    d_713_k_ = ((xs)[0]).WeakestPreOperands(0)
                    d_714_l_: int
                    d_714_l_ = ((xs)[0]).WeakestPreCapacity(0)
                    if (((xs)[0]).is_JUMPSeg) or (((xs)[0]).is_JUMPISeg):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JUMP/JUMPI: tgt address at the end: "))).VerbatimString(False))
                        d_715_r_: MiscTypes.Either
                        d_715_r_ = SegBuilder.default__.JUMPResolver((xs)[0])
                        source50_ = d_715_r_
                        if source50_.is_Left:
                            d_716___mcc_h0_ = source50_.l
                            d_717_v_ = d_716___mcc_h0_
                            source51_ = d_717_v_
                            if source51_.is_Value:
                                d_718___mcc_h2_ = source51_.v
                                d_719_address_ = d_718___mcc_h2_
                                _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (Hex.default__.NatToHex(d_719_address_))).VerbatimString(False))
                            elif True:
                                d_720___mcc_h3_ = source51_.s
                                d_721_msg_ = d_720___mcc_h3_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not determine stack value"))).VerbatimString(False))
                        elif True:
                            d_722___mcc_h1_ = source50_.r
                            d_723_stackPos_ = d_722___mcc_h1_
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Peek("))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_723_stackPos_))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    if ((xs)[0]).is_CONTSeg:
                        if (((((xs)[0]).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_724_nextPC_: int
                            d_724_nextPC_ = ((xs)[0]).StartAddressNextSeg()
                            _dafny.print(((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: PC of instruction after last is: "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex(d_724_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        elif True:
                            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CONT: has an invaid instructiom"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Operands:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_713_k_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WeakestPre Capacity:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_714_l_))
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
        d_725___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_725___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_725___accumulator_ = (d_725___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in75_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in75_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectJumpDestAsString(xs):
        d_726___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_726___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_726___accumulator_ = (d_726___accumulator_) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ensures s.IsJumpDest(0x"))) + (Hex.default__.NatToHex((xs)[0]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " as u256)\n"))))
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
        d_727_j_: _dafny.Seq
        d_727_j_ = default__.CollectJumpDestAsString(default__.CollectJumpDest(xs))
        if (len(d_727_j_)) > (0):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/** Lemma for Jumpdest */"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            _dafny.print((d_727_j_).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        default__.PrintProofObjectBody(xs, 0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def PrintProofObjectBody(xs, num):
        while True:
            with _dafny.label():
                if (len(xs)) > (0):
                    d_728_startAddress_: _dafny.Seq
                    d_728_startAddress_ = Hex.default__.NatToHex((((((xs)[0]).s).Ins())[0]).address)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n/** Code starting at 0x"))).VerbatimString(False))
                    _dafny.print((d_728_startAddress_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " */\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "function {:opaque} ExecuteFromTag_"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(num))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(s0: EvmState.ExecutingState): (s': EvmState.State)\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.PC() == 0x"))).VerbatimString(False))
                    _dafny.print((d_728_startAddress_).VerbatimString(False))
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
                                d_729___mcc_h0_ = source52_.l
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))).VerbatimString(False))
                            elif True:
                                d_730___mcc_h2_ = source52_.r
                                d_731_v_ = d_730___mcc_h2_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  requires s0.IsJumpDest(s0.Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_731_v_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "))\n"))).VerbatimString(False))
                    source53_ = (xs)[0]
                    if source53_.is_JUMP:
                        d_732___mcc_h4_ = source53_.s
                        d_733___mcc_h5_ = source53_.wpOp
                        d_734___mcc_h6_ = source53_.wpCap
                        d_735___mcc_h7_ = source53_.tgt
                        d_736___mcc_h8_ = source53_.stacks
                        d_737_tgt_ = d_735___mcc_h7_
                        d_738_s_ = d_732___mcc_h4_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() ==  "))).VerbatimString(False))
                        if True:
                            source54_ = d_737_tgt_
                            if source54_.is_Left:
                                d_739___mcc_h17_ = source54_.l
                                d_740_xc_ = d_739___mcc_h17_
                                source55_ = d_740_xc_
                                if source55_.is_Value:
                                    d_741___mcc_h19_ = source55_.v
                                    d_742_v_ = d_741___mcc_h19_
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))).VerbatimString(False))
                                    _dafny.print((Hex.default__.NatToHex((d_740_xc_).Extract())).VerbatimString(False))
                                elif True:
                                    d_743___mcc_h21_ = source55_.s
                                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Could not extract value "))).VerbatimString(False))
                            elif True:
                                d_744___mcc_h18_ = source54_.r
                                d_745_v_ = d_744___mcc_h18_
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s0.Peek("))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_745_v_))
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ") as nat"))).VerbatimString(False))
                        if ((((d_738_s_).lastIns).op).opcode) == (EVMConstants.default__.JUMPI):
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " || s'.PC() == 0x"))).VerbatimString(False))
                            _dafny.print((Hex.default__.NatToHex((((d_738_s_).lastIns).address) + (1))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        d_746_n_: int
                        d_746_n_ = ((xs)[0]).StackEffect()
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                        if (d_746_n_) >= (0):
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(d_746_n_))
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of((0) - (d_746_n_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif source53_.is_CONT:
                        d_747___mcc_h9_ = source53_.s
                        d_748___mcc_h10_ = source53_.wpOp
                        d_749___mcc_h11_ = source53_.wpCap
                        d_750___mcc_h12_ = source53_.stacks
                        d_751_s_ = d_747___mcc_h9_
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.EXECUTING?\n"))).VerbatimString(False))
                        if ((((d_751_s_).lastIns).op).opcode) != (EVMConstants.default__.INVALID):
                            d_752_nextPC_: int
                            d_752_nextPC_ = (d_751_s_).StartAddressNextSeg()
                            _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.PC() == 0x"))) + (Hex.default__.NatToHex(d_752_nextPC_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
                            d_753_n_: int
                            d_753_n_ = ((xs)[0]).StackEffect()
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  ensures s'.Operands() == s0.Operands()"))).VerbatimString(False))
                            if (d_753_n_) >= (0):
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " + "))).VerbatimString(False))
                                _dafny.print(_dafny.string_of(d_753_n_))
                            elif True:
                                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " - "))).VerbatimString(False))
                                _dafny.print(_dafny.string_of((0) - (d_753_n_)))
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  Last instruction is invalid"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    elif True:
                        d_754___mcc_h13_ = source53_.s
                        d_755___mcc_h14_ = source53_.wpOp
                        d_756___mcc_h15_ = source53_.wpCap
                        d_757___mcc_h16_ = source53_.stacks
                        d_758_s_ = d_754___mcc_h13_
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
                    d_759_k_: _dafny.Seq
                    d_759_k_ = PrettyIns.default__.PrintInstructionToDafny((xs)[0], pos, (pos) + (1))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
                    _dafny.print((d_759_k_).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    in79_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in80_ = (pos) + (1)
                    xs = in79_
                    pos = in80_
                    raise _dafny.TailCall()
                break

