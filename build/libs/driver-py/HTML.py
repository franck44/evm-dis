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
    def DOTSeg(s, numSeg):
        def iife24_(_pat_let11_0):
            def iife25_(d_871_r_):
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
            return iife25_(_pat_let11_0)
        d_870_jumpTip_ = (iife24_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_880_stackSizeEffect_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size "))) + (default__.DELTA__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " : ")))) + (Int.default__.IntToString((s).StackEffect()))
        d_881_mninNumOpe_ = ((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((s).WeakestPreOperands(0)))
        d_882_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</B><BR ALIGN=\"CENTER\"/>\n")))
        d_883_body_ = Instructions.default__.ToDot((s).Ins())
        return ((d_882_prefix_) + (d_883_body_), ((d_880_stackSizeEffect_) + (d_870_jumpTip_)) + (d_881_mninNumOpe_))

    @staticmethod
    def DOTSegTable(s, numSeg):
        def iife26_(_pat_let12_0):
            def iife27_(d_885_r_):
                def lambda44_(source58_):
                    if source58_.is_Left:
                        d_886___mcc_h0_ = source58_.l
                        d_887_v_ = d_886___mcc_h0_
                        source59_ = d_887_v_
                        if source59_.is_Value:
                            d_888___mcc_h2_ = source59_.v
                            d_889_address_ = d_888___mcc_h2_
                            return ((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Constant 0x")))) + (Hex.default__.NatToHex(d_889_address_))
                        elif True:
                            d_890___mcc_h3_ = source59_.s
                            d_891_msg_ = d_890___mcc_h3_
                            return (default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Unknown")))
                    elif True:
                        d_892___mcc_h1_ = source58_.r
                        d_893_stackPos_ = d_892___mcc_h1_
                        return (((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Stack on Entry.Peek(")))) + (Int.default__.NatToString(d_893_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

                return lambda44_(d_885_r_)
            return iife27_(_pat_let12_0)
        d_884_jumpTip_ = (iife26_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_894_tableStart_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE ALIGN=\"LEFT\" CELLBORDER=\"0\" BORDER=\"0\" cellpadding=\"0\"  CELLSPACING=\"1\">\n"))
        d_895_prefix_ = (((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">Segment ")))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"\" tooltip=\"Stack Size ")))) + (default__.DELTA__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": ")))) + (Int.default__.IntToString((s).StackEffect()))) + (default__.LINE__FEED__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((s).WeakestPreOperands(0)))) + (d_884_jumpTip_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "><FONT color=\"green\">")))) + (default__.INFO__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT></TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR><HR/>\n")))
        d_896_tableEnd_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>\n"))
        d_897_body_ = default__.DOTInsTable((s).Ins(), True)
        return (((d_894_tableStart_) + (d_895_prefix_)) + (d_897_body_)) + (d_896_tableEnd_)

    @staticmethod
    def DOTInsTable(xi, isFirst):
        d_898___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_898___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_899_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n"))
                    d_900_suffix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD></TR>\n"))
                    d_901_exitPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"exit\"")) if ((xi)[0]).IsJump() else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_902_entryPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"entry\"")) if isFirst else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_903_a_ = ((xi)[0]).ToHTMLTable(d_902_entryPortTag_, d_901_exitPortTag_)
                    d_898___accumulator_ = (d_898___accumulator_) + (((d_899_prefix_) + (d_903_a_)) + (d_900_suffix_))
                    in110_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    in111_ = False
                    xi = in110_
                    isFirst = in111_
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
