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
import PrettyPrinters
import CFGState
import Automata
import SeqOfSets
import PartitionMod
import GStateMinimiser
import Statistics

# Module: HTML

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Font(s, colour):
        return (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT"))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " COLOR=\""))) + (colour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"> "))) if (colour) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "> "))))) + (s)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))

    @staticmethod
    def RowTR(s):
        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR>"))) + (s)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR>\n")))

    @staticmethod
    def CellTD(body, align, border, sides, colspan, rowspan, bgcolour, cellspacing, cellpadding):
        return (((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ALIGN=\"")))) + (align)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BORDER=\"")))) + (border)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SIDES=\"")))) + (sides)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BGCOLOR=\"")))) + (bgcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLPADDING=\"")))) + (cellpadding)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLSPACING=\"")))) + (cellspacing)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "COLSPAN=\""))) + (colspan)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" "))) if (colspan) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0"))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ROWSPAN=\""))) + (rowspan)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" "))) if (rowspan) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1"))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (body)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>\n")))

    @staticmethod
    def Table(body, colour, bgcolour, cellborder, border, cellpadding, cellspacing):
        return (((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BORDER=\"")))) + (border)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLBORDER=\"")))) + (cellborder)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLPADDING=\"")))) + (cellpadding)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLSPACING=\"")))) + (cellspacing)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BGCOLOR=\"")))) + (bgcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "COLOR=\"")))) + (colour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (body)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>\n")))

    @staticmethod
    def DOTSeg(s, numSeg, minStackSize):
        def iife18_(_pat_let8_0):
            def iife19_(d_871_r_):
                def lambda43_(source56_):
                    if source56_.is_Left:
                        d_872___mcc_h0_ = source56_.l
                        d_873_v_ = d_872___mcc_h0_
                        source57_ = d_873_v_
                        if source57_.is_Value:
                            d_874___mcc_h2_ = source57_.v
                            d_875_address_ = d_874___mcc_h2_
                            return ((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Constant 0x")))) + (Hex.default__.NatToHex(d_875_address_))
                        elif True:
                            d_876___mcc_h3_ = source57_.s
                            d_877_msg_ = d_876___mcc_h3_
                            return (default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Unknown")))
                    elif True:
                        d_878___mcc_h1_ = source56_.r
                        d_879_stackPos_ = d_878___mcc_h1_
                        return (((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Stack on Entry.Peek(")))) + (Int.default__.NatToString(d_879_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

                return lambda43_(d_871_r_)
            return iife19_(_pat_let8_0)
        d_870_jumpTip_ = (iife18_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_880_stackSizeEffect_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size "))) + (default__.DELTA__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " : ")))) + (Int.default__.IntToString((s).StackEffect()))
        d_881_minNumOpe_ = ((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((s).WeakestPreOperands((s).Ins(), 0)))
        d_882_minNumOpAtNode_ = (((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment at this node ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((minStackSize).v)) if (minStackSize).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_883_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</B><BR ALIGN=\"CENTER\"/>\n")))
        d_884_body_ = Instructions.default__.ToDot((s).Ins())
        return ((d_883_prefix_) + (d_884_body_), (((d_880_stackSizeEffect_) + (d_870_jumpTip_)) + (d_881_minNumOpe_)) + (d_882_minNumOpAtNode_))

    @staticmethod
    def DOTSegTable(s, numSeg, minStackSize):
        def iife20_(_pat_let9_0):
            def iife21_(d_886_r_):
                def lambda44_(source58_):
                    if source58_.is_Left:
                        d_887___mcc_h0_ = source58_.l
                        d_888_v_ = d_887___mcc_h0_
                        source59_ = d_888_v_
                        if source59_.is_Value:
                            d_889___mcc_h2_ = source59_.v
                            d_890_address_ = d_889___mcc_h2_
                            return ((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Constant 0x")))) + (Hex.default__.NatToHex(d_890_address_))
                        elif True:
                            d_891___mcc_h3_ = source59_.s
                            d_892_msg_ = d_891___mcc_h3_
                            return (default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Unknown")))
                    elif True:
                        d_893___mcc_h1_ = source58_.r
                        d_894_stackPos_ = d_893___mcc_h1_
                        return (((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Stack on Entry.Peek(")))) + (Int.default__.NatToString(d_894_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

                return lambda44_(d_886_r_)
            return iife21_(_pat_let9_0)
        d_885_jumpTip_ = (iife20_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_895_tableStart_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE ALIGN=\"LEFT\" CELLBORDER=\"0\" BORDER=\"0\" cellpadding=\"0\"  CELLSPACING=\"1\">\n"))
        d_896_prefix_ = ((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">Segment ")))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"\" tooltip=\"Stack Size ")))) + (default__.DELTA__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": ")))) + (Int.default__.IntToString((s).StackEffect()))) + (default__.LINE__FEED__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((s).WeakestPreOperands((s).Ins(), 0)))) + ((((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment at this node ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((minStackSize).v)) if (minStackSize).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (d_885_jumpTip_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "><FONT color=\"green\">")))) + (default__.INFO__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT></TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR><HR/>\n")))
        d_897_tableEnd_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>\n"))
        d_898_body_ = default__.DOTInsTable((s).Ins(), True)
        return (((d_895_tableStart_) + (d_896_prefix_)) + (d_898_body_)) + (d_897_tableEnd_)

    @staticmethod
    def DOTInsTable(xi, isFirst):
        d_899___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_899___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_900_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n"))
                    d_901_suffix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD></TR>\n"))
                    d_902_exitPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"exit\"")) if ((xi)[0]).IsJump() else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_903_entryPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"entry\"")) if isFirst else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_904_a_ = ((xi)[0]).ToHTMLTable(d_903_entryPortTag_, d_902_exitPortTag_)
                    d_899___accumulator_ = (d_899___accumulator_) + (((d_900_prefix_) + (d_904_a_)) + (d_901_suffix_))
                    in113_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    in114_ = False
                    xi = in113_
                    isFirst = in114_
                    raise _dafny.TailCall()
                break

    @_dafny.classproperty
    def LINE__FEED__SYMBOL(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;"))
    @_dafny.classproperty
    def DELTA__SYMBOL(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#916;"))
    @_dafny.classproperty
    def LARGER__OR__EQ__SYMBOL(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#8805;"))
    @_dafny.classproperty
    def INFO__SYMBOL(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#8505;&#65039;"))
    @_dafny.classproperty
    def WHITE__SPACE__SYMBOL(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#160;"))
