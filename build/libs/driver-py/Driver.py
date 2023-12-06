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
import PrettyPrinters
import ProofObjectBuilder
import ArgParser
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph
import LoopResolver
import BuildCFGraph

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_994_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_994_optionParser_ = nw1_
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows (apply minimised only).")))
        (d_994_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-n")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_994_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_995_x_: _dafny.Seq
            d_995_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_995_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_994_optionParser_).PrintHelp()
        elif True:
            d_996_stringToProcess_: _dafny.Seq
            d_996_stringToProcess_ = (args)[(len(args)) - (1)]
            d_997_optArgs_: _dafny.Seq
            d_997_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_998_x_: _dafny.Seq
            d_998_x_ = BinaryDecoder.default__.Disassemble(d_996_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source72_ = (d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_997_optArgs_)
            if source72_.is_Success:
                d_999___mcc_h0_ = source72_.v
                PrettyPrinters.default__.PrintInstructions(d_998_x_)
            elif True:
                d_1000___mcc_h1_ = source72_.msg
                pass
            source73_ = (d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_997_optArgs_)
            if source73_.is_Success:
                d_1001___mcc_h2_ = source73_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_1002_y_: _dafny.Seq
                d_1002_y_ = Splitter.default__.SplitUpToTerminal(d_998_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_1002_y_, 0)
            elif True:
                d_1003___mcc_h3_ = source73_.msg
                pass
            source74_ = (d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_997_optArgs_)
            if source74_.is_Success:
                d_1004___mcc_h4_ = source74_.v
                d_1005_pathToDafnyLib_: _dafny.Seq
                def lambda60_(source75_):
                    if source75_.is_Success:
                        d_1006___mcc_h6_ = source75_.v
                        def iife65_(_pat_let32_0):
                            def iife66_(d_1007_p_):
                                return (d_1007_p_)[0]
                            return iife66_(_pat_let32_0)
                        return iife65_(d_1006___mcc_h6_)
                    elif True:
                        d_1008___mcc_h7_ = source75_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_1005_pathToDafnyLib_ = lambda60_((d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_997_optArgs_))
                d_1009_y_: _dafny.Seq
                d_1009_y_ = Splitter.default__.SplitUpToTerminal(d_998_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_1010_z_: _dafny.Seq
                d_1010_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1009_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_1010_z_, d_1005_pathToDafnyLib_)
            elif True:
                d_1011___mcc_h5_ = source74_.msg
                pass
            source76_ = (d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_997_optArgs_)
            if source76_.is_Success:
                d_1012___mcc_h8_ = source76_.v
                PrettyPrinters.default__.PrintInstructions(d_998_x_)
                d_1013_pathToDafnyLib_: _dafny.Seq
                def lambda61_(source77_):
                    if source77_.is_Success:
                        d_1014___mcc_h10_ = source77_.v
                        def iife67_(_pat_let33_0):
                            def iife68_(d_1015_p_):
                                return (d_1015_p_)[0]
                            return iife68_(_pat_let33_0)
                        return iife67_(d_1014___mcc_h10_)
                    elif True:
                        d_1016___mcc_h11_ = source77_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_1013_pathToDafnyLib_ = lambda61_((d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_997_optArgs_))
                d_1017_y_: _dafny.Seq
                d_1017_y_ = Splitter.default__.SplitUpToTerminal(d_998_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_1018_z_: _dafny.Seq
                d_1018_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1017_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_1018_z_, d_1013_pathToDafnyLib_)
            elif True:
                d_1019___mcc_h9_ = source76_.msg
                pass
            source78_ = (d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_997_optArgs_)
            if source78_.is_Success:
                d_1020___mcc_h12_ = source78_.v
                d_1021_m_ = d_1020___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_1022_y_: _dafny.Seq
                d_1022_y_ = Splitter.default__.SplitUpToTerminal(d_998_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_1022_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_1021_m_)[0])) == (0)) or (not(default__.IsNatNumber((d_1021_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_1023_maxDepth_: int
                    d_1023_maxDepth_ = default__.StringToNat((d_1021_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_1023_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1024_startAddress_: int
                    d_1024_startAddress_ = ((d_1022_y_)[0]).StartAddress()
                    pat_let_tv47_ = d_1024_startAddress_
                    d_1025_startState_: State.AState
                    def iife69_(_pat_let34_0):
                        def iife70_(d_1026_dt__update__tmp_h0_):
                            def iife71_(_pat_let35_0):
                                def iife72_(d_1027_dt__update_hpc_h0_):
                                    return State.AState_EState(d_1027_dt__update_hpc_h0_, (d_1026_dt__update__tmp_h0_).stack)
                                return iife72_(_pat_let35_0)
                            return iife71_(pat_let_tv47_)
                        return iife70_(_pat_let34_0)
                    d_1025_startState_ = iife69_(State.default__.DEFAULT__VALIDSTATE)
                    if (((d_1022_y_)[0]).StartAddress()) != (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment 0 does not start at address 0.\n"))).VerbatimString(False))
                    elif True:
                        d_1028_g_: CFGraph.BoolCFGraph
                        d_1028_g_ = BuildCFGraph.default__.BuildCFGV4(d_1022_y_, d_1023_maxDepth_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]))
                        if ((d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_997_optArgs_)).is_Success:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_1028_g_).DOTPrint(d_1022_y_, True, False)).VerbatimString(False))
                        elif True:
                            d_1029_fancy_: bool
                            d_1029_fancy_ = ((d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_997_optArgs_)).is_Success
                            d_1030_simple_: bool
                            d_1030_simple_ = (True if ((d_994_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), d_997_optArgs_)).is_Success else False)
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Computing Minimised CFG\n"))).VerbatimString(False))
                            d_1031_g_k_: CFGraph.BoolCFGraph
                            d_1031_g_k_ = (d_1028_g_).Minimise()
                            if not((d_1031_g_k_).IsValid()):
                                raise _dafny.HaltException("src/dafny/Driver.dfy(142,16): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_1031_g_k_).DOTPrint(d_1022_y_, d_1030_simple_, d_1029_fancy_)).VerbatimString(False))
            elif True:
                d_1032___mcc_h13_ = source78_.msg
                pass

    @staticmethod
    def CharToDigit(c):
        if (c) == (_dafny.CodePoint('0')):
            return MiscTypes.Option_Some(0)
        elif (c) == (_dafny.CodePoint('1')):
            return MiscTypes.Option_Some(1)
        elif (c) == (_dafny.CodePoint('2')):
            return MiscTypes.Option_Some(2)
        elif (c) == (_dafny.CodePoint('3')):
            return MiscTypes.Option_Some(3)
        elif (c) == (_dafny.CodePoint('4')):
            return MiscTypes.Option_Some(4)
        elif (c) == (_dafny.CodePoint('5')):
            return MiscTypes.Option_Some(5)
        elif (c) == (_dafny.CodePoint('6')):
            return MiscTypes.Option_Some(6)
        elif (c) == (_dafny.CodePoint('7')):
            return MiscTypes.Option_Some(7)
        elif (c) == (_dafny.CodePoint('8')):
            return MiscTypes.Option_Some(8)
        elif (c) == (_dafny.CodePoint('9')):
            return MiscTypes.Option_Some(9)
        elif True:
            return MiscTypes.Option_None()

    @staticmethod
    def IsNatNumber(s):
        while True:
            with _dafny.label():
                if (len(s)) == (1):
                    return (default__.CharToDigit((s)[0])).is_Some
                elif True:
                    source79_ = default__.CharToDigit((s)[0])
                    if source79_.is_None:
                        return False
                    elif True:
                        d_1033___mcc_h0_ = source79_.v
                        d_1034_v_ = d_1033___mcc_h0_
                        in146_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        s = in146_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_1035_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_1035_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

