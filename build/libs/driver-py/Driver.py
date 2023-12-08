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
import BuildCFGraph

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_999_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_999_optionParser_ = nw1_
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows.")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-n")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_999_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_1000_x_: _dafny.Seq
            d_1000_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Diassembled code:\n"))).VerbatimString(False))
            PrettyPrinters.default__.PrintInstructions(d_1000_x_)
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_999_optionParser_).PrintHelp()
        elif True:
            d_1001_stringToProcess_: _dafny.Seq
            d_1001_stringToProcess_ = (args)[(len(args)) - (1)]
            d_1002_x_: _dafny.Seq
            d_1002_x_ = BinaryDecoder.default__.Disassemble(d_1001_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            d_1003_optArgs_: _dafny.Seq
            d_1003_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_1004_disOpt_: bool
            d_1004_disOpt_ = (True if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_1003_optArgs_)).is_Success else False)
            d_1005_segmentOpt_: bool
            d_1005_segmentOpt_ = (True if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_1003_optArgs_)).is_Success else False)
            d_1006_proofOpt_: bool
            d_1006_proofOpt_ = (True if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_1003_optArgs_)).is_Success else False)
            d_1007_libOpt_: _dafny.Seq
            def lambda60_(source71_):
                if source71_.is_Success:
                    d_1008___mcc_h0_ = source71_.v
                    def iife71_(_pat_let35_0):
                        def iife72_(d_1009_p_):
                            return (d_1009_p_)[0]
                        return iife72_(_pat_let35_0)
                    return iife71_(d_1008___mcc_h0_)
                elif True:
                    d_1010___mcc_h1_ = source71_.msg
                    return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

            d_1007_libOpt_ = lambda60_((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_1003_optArgs_))
            d_1011_cfgDepthOpt_: int
            def lambda61_(source72_):
                if source72_.is_Success:
                    d_1012___mcc_h2_ = source72_.v
                    def iife73_(_pat_let36_0):
                        def iife74_(d_1013_args_):
                            return (Int.default__.StringToNat((d_1013_args_)[0], 0) if ((len((d_1013_args_)[0])) >= (1)) and (Int.default__.IsNatNumber((d_1013_args_)[0])) else 0)
                        return iife74_(_pat_let36_0)
                    return iife73_(d_1012___mcc_h2_)
                elif True:
                    d_1014___mcc_h3_ = source72_.msg
                    return 0

            d_1011_cfgDepthOpt_ = lambda61_((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1003_optArgs_))
            d_1015_rawOpt_: bool
            d_1015_rawOpt_ = (True if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_1003_optArgs_)).is_Success else False)
            d_1016_noTable_: bool
            d_1016_noTable_ = (True if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), d_1003_optArgs_)).is_Success else False)
            d_1017_fancy_: bool
            d_1017_fancy_ = (True if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_1003_optArgs_)).is_Success else False)
            if d_1004_disOpt_:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Diassembled code:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintInstructions(d_1002_x_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
            d_1018_y_: _dafny.Seq
            d_1018_y_ = Splitter.default__.SplitUpToTerminal(d_1002_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
            if d_1005_segmentOpt_:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintSegments(d_1018_y_, 0)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Segments -------------------\n"))).VerbatimString(False))
            if d_1006_proofOpt_:
                d_1019_z_: _dafny.Seq
                d_1019_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1018_y_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Dafny Proof Object:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintProofObjectToDafny(d_1019_z_, d_1007_libOpt_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Proof -------------------\n"))).VerbatimString(False))
            if (((d_1011_cfgDepthOpt_) > (0)) and ((len(d_1018_y_)) > (0))) and ((((d_1018_y_)[0]).StartAddress()) == (0)):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// maxDepth is:"))).VerbatimString(False))
                _dafny.print(_dafny.string_of(d_1011_cfgDepthOpt_))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                d_1020_jumpDests_: _dafny.Seq
                d_1020_jumpDests_ = ProofObjectBuilder.default__.CollectJumpDests(d_1018_y_)
                d_1021_g1_: tuple
                d_1021_g1_ = BuildCFGraph.default__.BuildCFGV5(d_1018_y_, d_1011_cfgDepthOpt_, d_1020_jumpDests_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({State.default__.DEFAULT__VALIDSTATE: CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}))
                d_1022_g_: CFGraph.BoolCFGraph
                d_1022_g_ = (d_1021_g1_)[0]
                if d_1015_rawOpt_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((d_1021_g1_)[1])))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(len((d_1022_g_).edges)))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Raw CFG\n"))).VerbatimString(False))
                    _dafny.print(((d_1022_g_).DOTPrint(d_1018_y_, d_1016_noTable_, d_1017_fancy_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Raw CFG -------------------\n"))).VerbatimString(False))
                elif True:
                    d_1023_g_k_: CFGraph.BoolCFGraph
                    d_1023_g_k_ = (d_1022_g_).Minimise()
                    if not((d_1023_g_k_).IsValid()):
                        raise _dafny.HaltException("src/dafny/Driver.dfy(134,10): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Size of minimised CFG: "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1023_g_k_).numNodes()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                    _dafny.print(_dafny.string_of((d_1023_g_k_).numEdges()))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Minimised CFG\n"))).VerbatimString(False))
                    _dafny.print(((d_1023_g_k_).DOTPrint(d_1018_y_, d_1016_noTable_, d_1017_fancy_)).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Minimised CFG -------------------\n"))).VerbatimString(False))
            elif True:
                if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1003_optArgs_)).is_Success:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found or --cfg argument is 0 or segment 0 does not start at pc=0\n"))).VerbatimString(False))

