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
import ProofObjectBuilder
import ArgParser
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph
import LoopResolver
import BuildCFGraphV2

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_1039_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_1039_optionParser_ = nw1_
        (d_1039_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_1039_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_1039_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_1039_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_1039_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_1039_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_1039_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows.")))
        (d_1039_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-n")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_1039_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_1040_x_: _dafny.Seq
            d_1040_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Diassembled code:\n"))).VerbatimString(False))
            PrettyPrinters.default__.PrintInstructions(d_1040_x_)
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_1039_optionParser_).PrintHelp()
        elif True:
            d_1041_stringToProcess_: _dafny.Seq
            d_1041_stringToProcess_ = (args)[(len(args)) - (1)]
            d_1042_x_: _dafny.Seq
            d_1042_x_ = BinaryDecoder.default__.Disassemble(d_1041_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            d_1043_optArgs_: _dafny.Seq
            d_1043_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_1044_disOpt_: bool
            d_1044_disOpt_ = (True if ((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_1043_optArgs_)).is_Success else False)
            d_1045_segmentOpt_: bool
            d_1045_segmentOpt_ = (True if ((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_1043_optArgs_)).is_Success else False)
            d_1046_proofOpt_: bool
            d_1046_proofOpt_ = (True if ((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_1043_optArgs_)).is_Success else False)
            d_1047_libOpt_: _dafny.Seq
            def lambda67_(source72_):
                if source72_.is_Success:
                    d_1048___mcc_h0_ = source72_.v
                    def iife77_(_pat_let38_0):
                        def iife78_(d_1049_p_):
                            return (d_1049_p_)[0]
                        return iife78_(_pat_let38_0)
                    return iife77_(d_1048___mcc_h0_)
                elif True:
                    d_1050___mcc_h1_ = source72_.msg
                    return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

            d_1047_libOpt_ = lambda67_((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_1043_optArgs_))
            d_1051_cfgDepthOpt_: int
            def lambda68_(source73_):
                if source73_.is_Success:
                    d_1052___mcc_h2_ = source73_.v
                    def iife79_(_pat_let39_0):
                        def iife80_(d_1053_args_):
                            return (Int.default__.StringToNat((d_1053_args_)[0], 0) if ((len((d_1053_args_)[0])) >= (1)) and (Int.default__.IsNatNumber((d_1053_args_)[0])) else 0)
                        return iife80_(_pat_let39_0)
                    return iife79_(d_1052___mcc_h2_)
                elif True:
                    d_1054___mcc_h3_ = source73_.msg
                    return 0

            d_1051_cfgDepthOpt_ = lambda68_((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1043_optArgs_))
            d_1055_rawOpt_: bool
            d_1055_rawOpt_ = (True if ((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_1043_optArgs_)).is_Success else False)
            d_1056_noTable_: bool
            d_1056_noTable_ = (True if ((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), d_1043_optArgs_)).is_Success else False)
            d_1057_fancy_: bool
            d_1057_fancy_ = (True if ((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_1043_optArgs_)).is_Success else False)
            if d_1044_disOpt_:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Diassembled code:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintInstructions(d_1042_x_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
            d_1058_y_: _dafny.Seq
            d_1058_y_ = Splitter.default__.SplitUpToTerminal(d_1042_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
            if d_1045_segmentOpt_:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintSegments(d_1058_y_, 0)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Segments -------------------\n"))).VerbatimString(False))
            if d_1046_proofOpt_:
                d_1059_z_: _dafny.Seq
                d_1059_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1058_y_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Dafny Proof Object:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintProofObjectToDafny(d_1059_z_, d_1047_libOpt_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Proof -------------------\n"))).VerbatimString(False))
            if (((d_1051_cfgDepthOpt_) > (0)) and ((len(d_1058_y_)) > (0))) and ((((d_1058_y_)[0]).StartAddress()) == (0)):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// maxDepth is:"))).VerbatimString(False))
                _dafny.print(_dafny.string_of(d_1051_cfgDepthOpt_))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                d_1060_jumpDests_: _dafny.Seq
                d_1060_jumpDests_ = ProofObjectBuilder.default__.CollectJumpDests(d_1058_y_)
                let_tmp_rhs2_ = BuildCFGraphV2.default__.BuildCFGV6(BuildCFGraphV2.Context_Context(d_1058_y_, d_1060_jumpDests_), d_1051_cfgDepthOpt_, 0, State.default__.DEFAULT__VALIDSTATE, BuildCFGraphV2.History_History(_dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({State.default__.DEFAULT__VALIDSTATE: CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))})), BuildCFGraphV2.default__.DEFAULT__STATS)
                d_1061_g1_ = let_tmp_rhs2_[0]
                d_1062_stats_ = let_tmp_rhs2_[1]
                d_1063_g_: CFGraph.BoolCFGraph
                d_1063_g_ = (d_1061_g1_).Graph()
                if d_1055_rawOpt_:
                    _dafny.print(((d_1062_stats_).PrettyPrint()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1063_g_).NumNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1063_g_).NumEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Raw CFG\n"))).VerbatimString(False))
                    _dafny.print(((d_1063_g_).DOTPrint(d_1058_y_, d_1056_noTable_, d_1057_fancy_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Raw CFG -------------------\n"))).VerbatimString(False))
                elif True:
                    d_1064_g_k_: CFGraph.BoolCFGraph
                    d_1064_g_k_ = (d_1063_g_).Minimise(False, _dafny.SeqWithoutIsStrInference([]))
                    if not((d_1064_g_k_).IsValid()):
                        raise _dafny.HaltException("src/dafny/Driver.dfy(134,10): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                    d_1065_g2_: CFGraph.BoolCFGraph
                    d_1065_g2_ = (d_1063_g_).Minimise(True, d_1058_y_)
                    _dafny.print(((d_1062_stats_).PrettyPrint()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of non-minimised CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1063_g_).NumNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1063_g_).NumEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of minimised CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1064_g_k_).NumNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1064_g_k_).NumEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of equiv-minimised CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1065_g2_).NumNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1065_g2_).NumEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Minimised CFG\n"))).VerbatimString(False))
                    _dafny.print(((d_1064_g_k_).DOTPrint(d_1058_y_, d_1056_noTable_, d_1057_fancy_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Minimised CFG -------------------\n"))).VerbatimString(False))
            elif True:
                if ((d_1039_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1043_optArgs_)).is_Success:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found or --cfg argument is 0 or segment 0 does not start at pc=0\n"))).VerbatimString(False))

