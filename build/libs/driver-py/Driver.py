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
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows (apply minimised only).")))
        (d_999_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-n")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_999_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_1000_x_: _dafny.Seq
            d_1000_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_1000_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_999_optionParser_).PrintHelp()
        elif True:
            d_1001_stringToProcess_: _dafny.Seq
            d_1001_stringToProcess_ = (args)[(len(args)) - (1)]
            d_1002_optArgs_: _dafny.Seq
            d_1002_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_1003_x_: _dafny.Seq
            d_1003_x_ = BinaryDecoder.default__.Disassemble(d_1001_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source71_ = (d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_1002_optArgs_)
            if source71_.is_Success:
                d_1004___mcc_h0_ = source71_.v
                PrettyPrinters.default__.PrintInstructions(d_1003_x_)
            elif True:
                d_1005___mcc_h1_ = source71_.msg
                pass
            source72_ = (d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_1002_optArgs_)
            if source72_.is_Success:
                d_1006___mcc_h2_ = source72_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_1007_y_: _dafny.Seq
                d_1007_y_ = Splitter.default__.SplitUpToTerminal(d_1003_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_1007_y_, 0)
            elif True:
                d_1008___mcc_h3_ = source72_.msg
                pass
            source73_ = (d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_1002_optArgs_)
            if source73_.is_Success:
                d_1009___mcc_h4_ = source73_.v
                d_1010_pathToDafnyLib_: _dafny.Seq
                def lambda60_(source74_):
                    if source74_.is_Success:
                        d_1011___mcc_h6_ = source74_.v
                        def iife71_(_pat_let35_0):
                            def iife72_(d_1012_p_):
                                return (d_1012_p_)[0]
                            return iife72_(_pat_let35_0)
                        return iife71_(d_1011___mcc_h6_)
                    elif True:
                        d_1013___mcc_h7_ = source74_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_1010_pathToDafnyLib_ = lambda60_((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_1002_optArgs_))
                d_1014_y_: _dafny.Seq
                d_1014_y_ = Splitter.default__.SplitUpToTerminal(d_1003_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_1015_z_: _dafny.Seq
                d_1015_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1014_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_1015_z_, d_1010_pathToDafnyLib_)
            elif True:
                d_1016___mcc_h5_ = source73_.msg
                pass
            source75_ = (d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_1002_optArgs_)
            if source75_.is_Success:
                d_1017___mcc_h8_ = source75_.v
                PrettyPrinters.default__.PrintInstructions(d_1003_x_)
                d_1018_pathToDafnyLib_: _dafny.Seq
                def lambda61_(source76_):
                    if source76_.is_Success:
                        d_1019___mcc_h10_ = source76_.v
                        def iife73_(_pat_let36_0):
                            def iife74_(d_1020_p_):
                                return (d_1020_p_)[0]
                            return iife74_(_pat_let36_0)
                        return iife73_(d_1019___mcc_h10_)
                    elif True:
                        d_1021___mcc_h11_ = source76_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_1018_pathToDafnyLib_ = lambda61_((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_1002_optArgs_))
                d_1022_y_: _dafny.Seq
                d_1022_y_ = Splitter.default__.SplitUpToTerminal(d_1003_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_1023_z_: _dafny.Seq
                d_1023_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1022_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_1023_z_, d_1018_pathToDafnyLib_)
            elif True:
                d_1024___mcc_h9_ = source75_.msg
                pass
            source77_ = (d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1002_optArgs_)
            if source77_.is_Success:
                d_1025___mcc_h12_ = source77_.v
                d_1026_m_ = d_1025___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_1027_y_: _dafny.Seq
                d_1027_y_ = Splitter.default__.SplitUpToTerminal(d_1003_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_1027_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_1026_m_)[0])) == (0)) or (not(Int.default__.IsNatNumber((d_1026_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_1028_maxDepth_: int
                    d_1028_maxDepth_ = Int.default__.StringToNat((d_1026_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_1028_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_1029_startAddress_: int
                    d_1029_startAddress_ = ((d_1027_y_)[0]).StartAddress()
                    pat_let_tv61_ = d_1029_startAddress_
                    d_1030_startState_: State.AState
                    def iife75_(_pat_let37_0):
                        def iife76_(d_1031_dt__update__tmp_h0_):
                            def iife77_(_pat_let38_0):
                                def iife78_(d_1032_dt__update_hpc_h0_):
                                    return State.AState_EState(d_1032_dt__update_hpc_h0_, (d_1031_dt__update__tmp_h0_).stack)
                                return iife78_(_pat_let38_0)
                            return iife77_(pat_let_tv61_)
                        return iife76_(_pat_let37_0)
                    d_1030_startState_ = iife75_(State.default__.DEFAULT__VALIDSTATE)
                    if (((d_1027_y_)[0]).StartAddress()) != (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment 0 does not start at address 0.\n"))).VerbatimString(False))
                    elif True:
                        d_1033_jumpDests_: _dafny.Seq
                        d_1033_jumpDests_ = ProofObjectBuilder.default__.CollectJumpDests(d_1027_y_)
                        d_1034_g1_: tuple
                        d_1034_g1_ = BuildCFGraph.default__.BuildCFGV5(d_1027_y_, d_1028_maxDepth_, d_1033_jumpDests_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({State.default__.DEFAULT__VALIDSTATE: CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}))
                        d_1035_g_: CFGraph.BoolCFGraph
                        d_1035_g_ = (d_1034_g1_)[0]
                        if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_1002_optArgs_)).is_Success:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of CFG: "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(len((d_1034_g1_)[1])))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of(len((d_1035_g_).edges)))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "edges\n"))).VerbatimString(False))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_1035_g_).DOTPrint(d_1027_y_, True, False)).VerbatimString(False))
                        elif True:
                            d_1036_fancy_: bool
                            d_1036_fancy_ = ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_1002_optArgs_)).is_Success
                            d_1037_simple_: bool
                            d_1037_simple_ = (True if ((d_999_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), d_1002_optArgs_)).is_Success else False)
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Computing Minimised CFG\n"))).VerbatimString(False))
                            d_1038_g_k_: CFGraph.BoolCFGraph
                            d_1038_g_k_ = (d_1035_g_).Minimise()
                            if not((d_1038_g_k_).IsValid()):
                                raise _dafny.HaltException("src/dafny/Driver.dfy(148,16): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of minimised CFG: "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of((d_1038_g_k_).numNodes()))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                            _dafny.print(_dafny.string_of((d_1038_g_k_).numEdges()))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_1038_g_k_).DOTPrint(d_1027_y_, d_1037_simple_, d_1036_fancy_)).VerbatimString(False))
            elif True:
                d_1039___mcc_h13_ = source77_.msg
                pass

