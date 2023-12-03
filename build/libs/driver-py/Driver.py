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
        d_959_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_959_optionParser_ = nw1_
        (d_959_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_959_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_959_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_959_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_959_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_959_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_959_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_959_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows (apply minimised only).")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_959_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_960_x_: _dafny.Seq
            d_960_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_960_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_959_optionParser_).PrintHelp()
        elif True:
            d_961_stringToProcess_: _dafny.Seq
            d_961_stringToProcess_ = (args)[(len(args)) - (1)]
            d_962_optArgs_: _dafny.Seq
            d_962_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_963_x_: _dafny.Seq
            d_963_x_ = BinaryDecoder.default__.Disassemble(d_961_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source70_ = (d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_962_optArgs_)
            if source70_.is_Success:
                d_964___mcc_h0_ = source70_.v
                PrettyPrinters.default__.PrintInstructions(d_963_x_)
            elif True:
                d_965___mcc_h1_ = source70_.msg
                pass
            source71_ = (d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_962_optArgs_)
            if source71_.is_Success:
                d_966___mcc_h2_ = source71_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_967_y_: _dafny.Seq
                d_967_y_ = Splitter.default__.SplitUpToTerminal(d_963_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_967_y_, 0)
            elif True:
                d_968___mcc_h3_ = source71_.msg
                pass
            source72_ = (d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_962_optArgs_)
            if source72_.is_Success:
                d_969___mcc_h4_ = source72_.v
                d_970_pathToDafnyLib_: _dafny.Seq
                def lambda58_(source73_):
                    if source73_.is_Success:
                        d_971___mcc_h6_ = source73_.v
                        def iife55_(_pat_let27_0):
                            def iife56_(d_972_p_):
                                return (d_972_p_)[0]
                            return iife56_(_pat_let27_0)
                        return iife55_(d_971___mcc_h6_)
                    elif True:
                        d_973___mcc_h7_ = source73_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_970_pathToDafnyLib_ = lambda58_((d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_962_optArgs_))
                d_974_y_: _dafny.Seq
                d_974_y_ = Splitter.default__.SplitUpToTerminal(d_963_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_975_z_: _dafny.Seq
                d_975_z_ = ProofObjectBuilder.default__.BuildProofObject(d_974_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_975_z_, d_970_pathToDafnyLib_)
            elif True:
                d_976___mcc_h5_ = source72_.msg
                pass
            source74_ = (d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_962_optArgs_)
            if source74_.is_Success:
                d_977___mcc_h8_ = source74_.v
                PrettyPrinters.default__.PrintInstructions(d_963_x_)
                d_978_pathToDafnyLib_: _dafny.Seq
                def lambda59_(source75_):
                    if source75_.is_Success:
                        d_979___mcc_h10_ = source75_.v
                        def iife57_(_pat_let28_0):
                            def iife58_(d_980_p_):
                                return (d_980_p_)[0]
                            return iife58_(_pat_let28_0)
                        return iife57_(d_979___mcc_h10_)
                    elif True:
                        d_981___mcc_h11_ = source75_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_978_pathToDafnyLib_ = lambda59_((d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_962_optArgs_))
                d_982_y_: _dafny.Seq
                d_982_y_ = Splitter.default__.SplitUpToTerminal(d_963_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_983_z_: _dafny.Seq
                d_983_z_ = ProofObjectBuilder.default__.BuildProofObject(d_982_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_983_z_, d_978_pathToDafnyLib_)
            elif True:
                d_984___mcc_h9_ = source74_.msg
                pass
            source76_ = (d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_962_optArgs_)
            if source76_.is_Success:
                d_985___mcc_h12_ = source76_.v
                d_986_m_ = d_985___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_987_y_: _dafny.Seq
                d_987_y_ = Splitter.default__.SplitUpToTerminal(d_963_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_987_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_986_m_)[0])) == (0)) or (not(default__.IsNatNumber((d_986_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_988_maxDepth_: int
                    d_988_maxDepth_ = default__.StringToNat((d_986_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_988_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_989_startAddress_: int
                    d_989_startAddress_ = ((d_987_y_)[0]).StartAddress()
                    pat_let_tv47_ = d_989_startAddress_
                    d_990_startState_: State.AState
                    def iife59_(_pat_let29_0):
                        def iife60_(d_991_dt__update__tmp_h0_):
                            def iife61_(_pat_let30_0):
                                def iife62_(d_992_dt__update_hpc_h0_):
                                    return State.AState_EState(d_992_dt__update_hpc_h0_, (d_991_dt__update__tmp_h0_).stack)
                                return iife62_(_pat_let30_0)
                            return iife61_(pat_let_tv47_)
                        return iife60_(_pat_let29_0)
                    d_990_startState_ = iife59_(State.default__.DEFAULT__VALIDSTATE)
                    if (((d_987_y_)[0]).StartAddress()) != (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment 0 does not start at address 0.\n"))).VerbatimString(False))
                    elif True:
                        d_993_g_: CFGraph.BoolCFGraph
                        d_993_g_ = BuildCFGraph.default__.BuildCFGV4(d_987_y_, d_988_maxDepth_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]))
                        if ((d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_962_optArgs_)).is_Success:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_993_g_).DOTPrint(d_987_y_, False)).VerbatimString(False))
                        d_994_fancy_: bool
                        d_994_fancy_ = ((d_959_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_962_optArgs_)).is_Success
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Computing Minimised CFG\n"))).VerbatimString(False))
                        d_995_g_k_: CFGraph.BoolCFGraph
                        d_995_g_k_ = (d_993_g_).Minimise()
                        if not((d_995_g_k_).IsValid()):
                            raise _dafny.HaltException("src/dafny/Driver.dfy(140,14): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                        _dafny.print(((d_995_g_k_).DOTPrint(d_987_y_, d_994_fancy_)).VerbatimString(False))
            elif True:
                d_996___mcc_h13_ = source76_.msg
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
                    source77_ = default__.CharToDigit((s)[0])
                    if source77_.is_None:
                        return False
                    elif True:
                        d_997___mcc_h0_ = source77_.v
                        d_998_v_ = d_997___mcc_h0_
                        in145_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        s = in145_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_999_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_999_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

