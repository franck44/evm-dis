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
import CFGState
import ProofObject
import PrettyIns
import PrettyPrinters
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
    def CellTD(body, align, fixedsize, width, border, sides, colspan, rowspan, bgcolour, cellspacing, cellpadding, href, tooltip):
        return (((((((((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ALIGN=\"")))) + (align)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "fixedsize=\"")))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if fixedsize else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "WIDTH=\""))) + (width)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" "))) if (width) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BORDER=\"")))) + (border)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SIDES=\"")))) + (sides)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BGCOLOR=\""))) + (bgcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" "))) if (bgcolour) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLPADDING=\"")))) + (cellpadding)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLSPACING=\"")))) + (cellspacing)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "COLSPAN=\""))) + (colspan)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" "))) if (colspan) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0"))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ROWSPAN=\""))) + (rowspan)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" "))) if (rowspan) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1"))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "href=\"")))) + (href)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\""))) + (tooltip)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" "))) if (tooltip) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (body)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>\n")))

    @staticmethod
    def Table(body, align, colour, bgcolour, cellborder, border, cellpadding, cellspacing):
        return ((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ALIGN=\"")))) + (align)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BORDER=\"")))) + (border)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLBORDER=\"")))) + (cellborder)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLPADDING=\"")))) + (cellpadding)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CELLSPACING=\"")))) + (cellspacing)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "BGCOLOR=\""))) + (bgcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" "))) if (bgcolour) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "COLOR=\"")))) + (colour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (body)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>\n")))

    @staticmethod
    def DOTSeg(s, numSeg, minStackSize, index):
        def iife18_(_pat_let8_0):
            def iife19_(d_897_r_):
                def lambda43_(source58_):
                    if source58_.is_Left:
                        d_898___mcc_h0_ = source58_.l
                        d_899_v_ = d_898___mcc_h0_
                        source59_ = d_899_v_
                        if source59_.is_Value:
                            d_900___mcc_h2_ = source59_.v
                            d_901_address_ = d_900___mcc_h2_
                            return ((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Constant 0x")))) + (Hex.default__.NatToHex(d_901_address_))
                        elif True:
                            d_902___mcc_h3_ = source59_.s
                            d_903_msg_ = d_902___mcc_h3_
                            return (default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Unknown")))
                    elif True:
                        d_904___mcc_h1_ = source58_.r
                        d_905_stackPos_ = d_904___mcc_h1_
                        return (((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Stack on Entry.Peek(")))) + (Int.default__.NatToString(d_905_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

                return lambda43_(d_897_r_)
            return iife19_(_pat_let8_0)
        d_896_jumpTip_ = (iife18_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_906_stackSizeEffect_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size "))) + (default__.DELTA__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " : ")))) + (Int.default__.IntToString((s).StackEffect()))
        d_907_minNumOpe_ = ((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((s).WeakestPreOperands((s).Ins(), 0)))
        d_908_minNumOpAtNode_ = (((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment at this node ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((minStackSize).v)) if (minStackSize).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_909_prefix_ = (((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#")))) + (Int.default__.NatToString(index))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "|")))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</B><BR ALIGN=\"CENTER\"/>\n")))
        d_910_body_ = Instructions.default__.ToDot((s).Ins())
        return ((d_909_prefix_) + (d_910_body_), (((d_906_stackSizeEffect_) + (d_896_jumpTip_)) + (d_907_minNumOpe_)) + (d_908_minNumOpAtNode_))

    @staticmethod
    def DOTSegTable(s, a, minStackSize, index):
        def iife20_(_pat_let9_0):
            def iife21_(d_912_r_):
                def lambda44_(source60_):
                    if source60_.is_Left:
                        d_913___mcc_h0_ = source60_.l
                        d_914_v_ = d_913___mcc_h0_
                        source61_ = d_914_v_
                        if source61_.is_Value:
                            d_915___mcc_h2_ = source61_.v
                            d_916_address_ = d_915___mcc_h2_
                            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Constant 0x"))) + (Hex.default__.NatToHex(d_916_address_))
                        elif True:
                            d_917___mcc_h3_ = source61_.s
                            d_918_msg_ = d_917___mcc_h3_
                            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Unknown"))
                    elif True:
                        d_919___mcc_h1_ = source60_.r
                        d_920_stackPos_ = d_919___mcc_h1_
                        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Stack on Entry.Peek("))) + (Int.default__.NatToString(d_920_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

                return lambda44_(d_912_r_)
            return iife21_(_pat_let9_0)
        d_911_jumpTip_ = (iife20_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_921_gasSymbol_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981; "))
        return default__.Table(((default__.RowTR(((default__.CellTD((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#"))) + (Int.default__.NatToString(index))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "|")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment ")))) + (Int.default__.NatToString((a).segNum))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]"))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "left")), False, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))) + (default__.CellTD(default__.Font(default__.INFO__SYMBOL, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "left")), False, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), ((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size "))) + (default__.DELTA__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": ")))) + (Int.default__.IntToString((s).StackEffect()))) + (default__.LINE__FEED__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Abstract stack at this node: [")))) + ((a).StackToHTML())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))) + ((((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry at this node ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((minStackSize).v)) if (minStackSize).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (default__.LINE__FEED__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((s).WeakestPreOperands((s).Ins(), 0)))) + (((default__.LINE__FEED__SYMBOL) + (d_911_jumpTip_) if (d_911_jumpTip_) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))))) + (default__.CellTD(d_921_gasSymbol_, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "left")), False, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lots of gas!")))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<HR/>")))) + (default__.DOTInsTable((s).Ins(), True)), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "left")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "black")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1")))

    @staticmethod
    def DOTInsTable(xi, isFirst):
        d_922___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_922___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_923_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n"))
                    d_924_suffix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD></TR>\n"))
                    d_925_exitPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"exit\"")) if ((xi)[0]).IsJump() else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_926_entryPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"entry\"")) if isFirst else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_927_a_ = ((xi)[0]).ToHTMLTable(d_926_entryPortTag_, d_925_exitPortTag_)
                    d_922___accumulator_ = (d_922___accumulator_) + (((d_923_prefix_) + (d_927_a_)) + (d_924_suffix_))
                    in128_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    in129_ = False
                    xi = in128_
                    isFirst = in129_
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
