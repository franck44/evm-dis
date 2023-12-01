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
        d_949_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_949_optionParser_ = nw1_
        (d_949_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_949_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_949_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_949_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_949_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_949_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_949_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_949_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows (apply minimised only).")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_949_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_950_x_: _dafny.Seq
            d_950_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_950_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_949_optionParser_).PrintHelp()
        elif True:
            d_951_stringToProcess_: _dafny.Seq
            d_951_stringToProcess_ = (args)[(len(args)) - (1)]
            d_952_optArgs_: _dafny.Seq
            d_952_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_953_x_: _dafny.Seq
            d_953_x_ = BinaryDecoder.default__.Disassemble(d_951_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source68_ = (d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_952_optArgs_)
            if source68_.is_Success:
                d_954___mcc_h0_ = source68_.v
                PrettyPrinters.default__.PrintInstructions(d_953_x_)
            elif True:
                d_955___mcc_h1_ = source68_.msg
                pass
            source69_ = (d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_952_optArgs_)
            if source69_.is_Success:
                d_956___mcc_h2_ = source69_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_957_y_: _dafny.Seq
                d_957_y_ = Splitter.default__.SplitUpToTerminal(d_953_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_957_y_, 0)
            elif True:
                d_958___mcc_h3_ = source69_.msg
                pass
            source70_ = (d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_952_optArgs_)
            if source70_.is_Success:
                d_959___mcc_h4_ = source70_.v
                d_960_pathToDafnyLib_: _dafny.Seq
                def lambda56_(source71_):
                    if source71_.is_Success:
                        d_961___mcc_h6_ = source71_.v
                        def iife45_(_pat_let22_0):
                            def iife46_(d_962_p_):
                                return (d_962_p_)[0]
                            return iife46_(_pat_let22_0)
                        return iife45_(d_961___mcc_h6_)
                    elif True:
                        d_963___mcc_h7_ = source71_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_960_pathToDafnyLib_ = lambda56_((d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_952_optArgs_))
                d_964_y_: _dafny.Seq
                d_964_y_ = Splitter.default__.SplitUpToTerminal(d_953_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_965_z_: _dafny.Seq
                d_965_z_ = ProofObjectBuilder.default__.BuildProofObject(d_964_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_965_z_, d_960_pathToDafnyLib_)
            elif True:
                d_966___mcc_h5_ = source70_.msg
                pass
            source72_ = (d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_952_optArgs_)
            if source72_.is_Success:
                d_967___mcc_h8_ = source72_.v
                PrettyPrinters.default__.PrintInstructions(d_953_x_)
                d_968_pathToDafnyLib_: _dafny.Seq
                def lambda57_(source73_):
                    if source73_.is_Success:
                        d_969___mcc_h10_ = source73_.v
                        def iife47_(_pat_let23_0):
                            def iife48_(d_970_p_):
                                return (d_970_p_)[0]
                            return iife48_(_pat_let23_0)
                        return iife47_(d_969___mcc_h10_)
                    elif True:
                        d_971___mcc_h11_ = source73_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_968_pathToDafnyLib_ = lambda57_((d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_952_optArgs_))
                d_972_y_: _dafny.Seq
                d_972_y_ = Splitter.default__.SplitUpToTerminal(d_953_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_973_z_: _dafny.Seq
                d_973_z_ = ProofObjectBuilder.default__.BuildProofObject(d_972_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_973_z_, d_968_pathToDafnyLib_)
            elif True:
                d_974___mcc_h9_ = source72_.msg
                pass
            source74_ = (d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_952_optArgs_)
            if source74_.is_Success:
                d_975___mcc_h12_ = source74_.v
                d_976_m_ = d_975___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_977_y_: _dafny.Seq
                d_977_y_ = Splitter.default__.SplitUpToTerminal(d_953_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_977_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_976_m_)[0])) == (0)) or (not(default__.IsNatNumber((d_976_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_978_maxDepth_: int
                    d_978_maxDepth_ = default__.StringToNat((d_976_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_978_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_979_startAddress_: int
                    d_979_startAddress_ = ((d_977_y_)[0]).StartAddress()
                    pat_let_tv47_ = d_979_startAddress_
                    d_980_startState_: State.AState
                    def iife49_(_pat_let24_0):
                        def iife50_(d_981_dt__update__tmp_h0_):
                            def iife51_(_pat_let25_0):
                                def iife52_(d_982_dt__update_hpc_h0_):
                                    return State.AState_EState(d_982_dt__update_hpc_h0_, (d_981_dt__update__tmp_h0_).stack)
                                return iife52_(_pat_let25_0)
                            return iife51_(pat_let_tv47_)
                        return iife50_(_pat_let24_0)
                    d_980_startState_ = iife49_(State.default__.DEFAULT__VALIDSTATE)
                    if (((d_977_y_)[0]).StartAddress()) != (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment 0 does not start at address 0.\n"))).VerbatimString(False))
                    elif True:
                        d_983_g_: CFGraph.BoolCFGraph
                        d_983_g_ = BuildCFGraph.default__.BuildCFGV4(d_977_y_, d_978_maxDepth_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]))
                        if ((d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_952_optArgs_)).is_Success:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_983_g_).DOTPrint(d_977_y_, False)).VerbatimString(False))
                        d_984_fancy_: bool
                        d_984_fancy_ = ((d_949_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_952_optArgs_)).is_Success
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Computing Minimised CFG\n"))).VerbatimString(False))
                        d_985_g_k_: CFGraph.BoolCFGraph
                        d_985_g_k_ = (d_983_g_).Minimise()
                        if not((d_985_g_k_).IsValid()):
                            raise _dafny.HaltException("src/dafny/Driver.dfy(140,14): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                        _dafny.print(((d_985_g_k_).DOTPrint(d_977_y_, d_984_fancy_)).VerbatimString(False))
            elif True:
                d_986___mcc_h13_ = source74_.msg
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
                    source75_ = default__.CharToDigit((s)[0])
                    if source75_.is_None:
                        return False
                    elif True:
                        d_987___mcc_h0_ = source75_.v
                        d_988_v_ = d_987___mcc_h0_
                        in145_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        s = in145_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_989_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_989_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

