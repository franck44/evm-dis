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
import EVMObject
import ArgParser
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph
import LoopResolver
import BuildCFGraph
import ProofObjectBuilder

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_1051_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_1051_optionParser_ = nw1_
        (d_1051_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_1051_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_1051_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_1051_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_1051_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_1051_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_1051_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows.")))
        (d_1051_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-n")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_1051_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_1052_x_: _dafny.Seq
            d_1052_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Diassembled code:\n"))).VerbatimString(False))
            PrettyPrinters.default__.PrintInstructions(d_1052_x_)
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_1051_optionParser_).PrintHelp()
        elif True:
            d_1053_stringToProcess_: _dafny.Seq
            d_1053_stringToProcess_ = (args)[(len(args)) - (1)]
            d_1054_x_: _dafny.Seq
            d_1054_x_ = BinaryDecoder.default__.Disassemble(d_1053_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            d_1055_optArgs_: _dafny.Seq
            d_1055_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_1056_disOpt_: bool
            d_1056_disOpt_ = (True if ((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_1055_optArgs_)).is_Success else False)
            d_1057_segmentOpt_: bool
            d_1057_segmentOpt_ = (True if ((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_1055_optArgs_)).is_Success else False)
            d_1058_proofOpt_: bool
            d_1058_proofOpt_ = (True if ((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_1055_optArgs_)).is_Success else False)
            d_1059_libOpt_: _dafny.Seq
            def lambda73_(source72_):
                if source72_.is_Success:
                    d_1060___mcc_h0_ = source72_.v
                    def iife85_(_pat_let42_0):
                        def iife86_(d_1061_p_):
                            return (d_1061_p_)[0]
                        return iife86_(_pat_let42_0)
                    return iife85_(d_1060___mcc_h0_)
                elif True:
                    d_1062___mcc_h1_ = source72_.msg
                    return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

            d_1059_libOpt_ = lambda73_((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_1055_optArgs_))
            d_1063_cfgDepthOpt_: int
            def lambda74_(source73_):
                if source73_.is_Success:
                    d_1064___mcc_h2_ = source73_.v
                    def iife87_(_pat_let43_0):
                        def iife88_(d_1065_args_):
                            return (Int.default__.StringToNat((d_1065_args_)[0], 0) if ((len((d_1065_args_)[0])) >= (1)) and (Int.default__.IsNatNumber((d_1065_args_)[0])) else 0)
                        return iife88_(_pat_let43_0)
                    return iife87_(d_1064___mcc_h2_)
                elif True:
                    d_1066___mcc_h3_ = source73_.msg
                    return 0

            d_1063_cfgDepthOpt_ = lambda74_((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1055_optArgs_))
            d_1067_rawOpt_: bool
            d_1067_rawOpt_ = (True if ((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_1055_optArgs_)).is_Success else False)
            d_1068_noTable_: bool
            d_1068_noTable_ = (True if ((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), d_1055_optArgs_)).is_Success else False)
            d_1069_fancy_: bool
            d_1069_fancy_ = (True if ((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_1055_optArgs_)).is_Success else False)
            if d_1056_disOpt_:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Diassembled code:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintInstructions(d_1054_x_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
            d_1070_y_: _dafny.Seq
            d_1070_y_ = Splitter.default__.SplitUpToTerminal(d_1054_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
            d_1071_prog_: EVMObject.EVMObj
            d_1071_prog_ = EVMObject.EVMObj_EVMObj(d_1070_y_, EVMObject.default__.CollectJumpDests(d_1070_y_))
            if d_1057_segmentOpt_:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintSegments(d_1070_y_, 0)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Segments -------------------\n"))).VerbatimString(False))
            if d_1058_proofOpt_:
                d_1072_z_: _dafny.Seq
                d_1072_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1070_y_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Dafny Proof Object:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintProofObjectToDafny(d_1072_z_, d_1059_libOpt_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Proof -------------------\n"))).VerbatimString(False))
            if (((d_1063_cfgDepthOpt_) > (0)) and ((len(d_1070_y_)) > (0))) and ((((d_1070_y_)[0]).StartAddress()) == (0)):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// maxDepth is:"))).VerbatimString(False))
                _dafny.print(_dafny.string_of(d_1063_cfgDepthOpt_))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                let_tmp_rhs2_ = BuildCFGraph.default__.BuildCFGV6(d_1071_prog_, d_1063_cfgDepthOpt_, 0, State.default__.DEFAULT__VALIDSTATE, BuildCFGraph.default__.DEFAULT__HISTORY, BuildCFGraph.default__.DEFAULT__STATS)
                d_1073_g1_ = let_tmp_rhs2_[0]
                d_1074_stats_ = let_tmp_rhs2_[1]
                d_1075_g_: CFGraph.BoolCFGraph
                d_1075_g_ = (d_1073_g1_).Graph()
                if d_1067_rawOpt_:
                    _dafny.print(((d_1074_stats_).PrettyPrint()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1075_g_).NumNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1075_g_).NumEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Raw CFG\n"))).VerbatimString(False))
                    _dafny.print(((d_1075_g_).DOTPrint(d_1070_y_, d_1068_noTable_, d_1069_fancy_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Raw CFG -------------------\n"))).VerbatimString(False))
                elif True:
                    d_1076_g_k_: CFGraph.BoolCFGraph
                    d_1076_g_k_ = (d_1075_g_).Minimise(False, _dafny.SeqWithoutIsStrInference([]))
                    if not((d_1076_g_k_).IsValid()):
                        raise _dafny.HaltException("src/dafny/Driver.dfy(135,10): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                    d_1077_g2_: CFGraph.BoolCFGraph
                    d_1077_g2_ = (d_1075_g_).Minimise(True, d_1070_y_)
                    _dafny.print(((d_1074_stats_).PrettyPrint()).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of non-minimised CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1075_g_).NumNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1075_g_).NumEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of minimised CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1076_g_k_).NumNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1076_g_k_).NumEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of equiv-minimised CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1077_g2_).NumNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1077_g2_).NumEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Minimised CFG\n"))).VerbatimString(False))
                    _dafny.print(((d_1076_g_k_).DOTPrint(d_1070_y_, d_1068_noTable_, d_1069_fancy_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Minimised CFG -------------------\n"))).VerbatimString(False))
            elif True:
                if ((d_1051_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1055_optArgs_)).is_Success:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found or --cfg argument is 0 or segment 0 does not start at pc=0\n"))).VerbatimString(False))

