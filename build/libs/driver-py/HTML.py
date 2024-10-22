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
import PrettyPrinters as PrettyPrinters
import Automata as Automata
import SeqOfSets as SeqOfSets
import PartitionMod as PartitionMod
import GStateMinimiser as GStateMinimiser
import Statistics as Statistics

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
        def iife0_(_pat_let8_0):
            def iife1_(d_1_r_):
                def lambda0_():
                    source0_ = d_1_r_
                    if True:
                        if source0_.is_Left:
                            d_2_v_ = source0_.l
                            source1_ = d_2_v_
                            if True:
                                if source1_.is_Value:
                                    d_3_address_ = source1_.v
                                    return ((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Constant 0x")))) + (Hex.default__.NatToHex(d_3_address_))
                            if True:
                                d_4_msg_ = source1_.s
                                return (default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Unknown")))
                    if True:
                        d_5_stackPos_ = source0_.r
                        return (((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Stack on Entry.Peek(")))) + (Int.default__.NatToString(d_5_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

                return lambda0_()
            return iife1_(_pat_let8_0)
        d_0_jumpTip_ = (iife0_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_6_stackSizeEffect_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size "))) + (default__.DELTA__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " : ")))) + (Int.default__.IntToString((s).StackEffect()))
        d_7_minNumOpe_ = ((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((s).WeakestPreOperands((s).Ins(), 0)))
        d_8_minNumOpAtNode_ = (((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment at this node ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((minStackSize).v)) if (minStackSize).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_9_prefix_ = (((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#")))) + (Int.default__.NatToString(index))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "|")))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</B><BR ALIGN=\"CENTER\"/>\n")))
        d_10_body_ = Instructions.default__.ToDot((s).Ins())
        return ((d_9_prefix_) + (d_10_body_), (((d_6_stackSizeEffect_) + (d_0_jumpTip_)) + (d_7_minNumOpe_)) + (d_8_minNumOpAtNode_))

    @staticmethod
    def DOTSegTable(s, a, minStackSize, index):
        def iife0_(_pat_let9_0):
            def iife1_(d_1_r_):
                def lambda0_():
                    source0_ = d_1_r_
                    if True:
                        if source0_.is_Left:
                            d_2_v_ = source0_.l
                            source1_ = d_2_v_
                            if True:
                                if source1_.is_Value:
                                    d_3_address_ = source1_.v
                                    return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Constant 0x"))) + (Hex.default__.NatToHex(d_3_address_))
                            if True:
                                d_4_msg_ = source1_.s
                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Unknown"))
                    if True:
                        d_5_stackPos_ = source0_.r
                        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit Jump target: Stack on Entry.Peek("))) + (Int.default__.NatToString(d_5_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))

                return lambda0_()
            return iife1_(_pat_let9_0)
        d_0_jumpTip_ = (iife0_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_6_gasSymbol_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981; "))
        return default__.Table(((default__.RowTR(((default__.CellTD((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#"))) + (Int.default__.NatToString(index))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "|")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment ")))) + (Int.default__.NatToString((a).segNum))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]"))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "left")), False, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))) + (default__.CellTD(default__.Font(default__.INFO__SYMBOL, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "left")), False, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), ((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size "))) + (default__.DELTA__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": ")))) + (Int.default__.IntToString((s).StackEffect()))) + (default__.LINE__FEED__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Abstract stack at this node: [")))) + ((a).StackToHTML())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))) + ((((((default__.LINE__FEED__SYMBOL) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry at this node ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((minStackSize).v)) if (minStackSize).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))) + (default__.LINE__FEED__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size on Entry for this segment ")))) + (default__.LARGER__OR__EQ__SYMBOL)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (Int.default__.NatToString((s).WeakestPreOperands((s).Ins(), 0)))) + (((default__.LINE__FEED__SYMBOL) + (d_0_jumpTip_) if (d_0_jumpTip_) != (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))))) + (default__.CellTD(d_6_gasSymbol_, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "left")), False, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lots of gas!")))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<HR/>")))) + (default__.DOTInsTable((s).Ins(), True)), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "left")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "black")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1")))

    @staticmethod
    def DOTInsTable(xi, isFirst):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_1_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n"))
                    d_2_suffix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD></TR>\n"))
                    d_3_exitPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"exit\"")) if ((xi)[0]).IsJump() else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_4_entryPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"entry\"")) if isFirst else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_5_a_ = ((xi)[0]).ToHTMLTable(d_4_entryPortTag_, d_3_exitPortTag_)
                    d_0___accumulator_ = (d_0___accumulator_) + (((d_1_prefix_) + (d_5_a_)) + (d_2_suffix_))
                    in0_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    in1_ = False
                    xi = in0_
                    isFirst = in1_
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
