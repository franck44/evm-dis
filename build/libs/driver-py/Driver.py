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
import HTML
import EVMObject
import ArgParser
import ProofObjectBuilder

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_1018_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_1018_optionParser_ = nw1_
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows.")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-n")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-t")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--title")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The name of the program.")))
        (d_1018_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-i")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--info")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The stats of the program (size, segments).")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_1018_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            if (len((args)[1])) == (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty \n"))).VerbatimString(False))
            elif (_dafny.euclidian_modulus(len((args)[1]), 2)) != (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty and have even length, length is "))).VerbatimString(False))
                _dafny.print(_dafny.string_of(len((args)[1])))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            elif Hex.default__.IsHexString((_dafny.SeqWithoutIsStrInference(((args)[1])[2::]) if (_dafny.SeqWithoutIsStrInference(((args)[1])[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else (args)[1])):
                d_1019_x_: _dafny.Seq
                d_1019_x_ = BinaryDecoder.default__.Disassemble((_dafny.SeqWithoutIsStrInference(((args)[1])[2::]) if (_dafny.SeqWithoutIsStrInference(((args)[1])[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else (args)[1]), _dafny.SeqWithoutIsStrInference([]), 0)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassembled code:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintInstructions(d_1019_x_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
            elif True:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be hexadecimal\n"))).VerbatimString(False))
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_1018_optionParser_).PrintHelp()
        elif True:
            d_1020_stringToProcess_: _dafny.Seq
            d_1020_stringToProcess_ = (args)[(len(args)) - (1)]
            if (len(d_1020_stringToProcess_)) == (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty \n"))).VerbatimString(False))
            elif (_dafny.euclidian_modulus(len(d_1020_stringToProcess_), 2)) != (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must have even length, length is "))).VerbatimString(False))
                _dafny.print(_dafny.string_of(len(d_1020_stringToProcess_)))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            elif not(Hex.default__.IsHexString((_dafny.SeqWithoutIsStrInference((d_1020_stringToProcess_)[2::]) if (_dafny.SeqWithoutIsStrInference((d_1020_stringToProcess_)[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else d_1020_stringToProcess_))):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be hexadecimal\n"))).VerbatimString(False))
            elif True:
                d_1021_x_: _dafny.Seq
                d_1021_x_ = BinaryDecoder.default__.Disassemble((_dafny.SeqWithoutIsStrInference((d_1020_stringToProcess_)[2::]) if (_dafny.SeqWithoutIsStrInference((d_1020_stringToProcess_)[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else d_1020_stringToProcess_), _dafny.SeqWithoutIsStrInference([]), 0)
                d_1022_optArgs_: _dafny.Seq
                d_1022_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
                d_1023_disOpt_: bool
                d_1023_disOpt_ = (True if ((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_1022_optArgs_)).is_Success else False)
                d_1024_segmentOpt_: bool
                d_1024_segmentOpt_ = (True if ((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_1022_optArgs_)).is_Success else False)
                d_1025_proofOpt_: bool
                d_1025_proofOpt_ = (True if ((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_1022_optArgs_)).is_Success else False)
                d_1026_libOpt_: _dafny.Seq
                def lambda71_(source70_):
                    if source70_.is_Success:
                        d_1027___mcc_h0_ = source70_.v
                        d_1028_p_ = d_1027___mcc_h0_
                        return (d_1028_p_)[0]
                    elif True:
                        d_1029___mcc_h1_ = source70_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_1026_libOpt_ = lambda71_((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_1022_optArgs_))
                d_1030_cfgDepthOpt_: int
                def lambda72_(source71_):
                    if source71_.is_Success:
                        d_1031___mcc_h2_ = source71_.v
                        d_1032_args_ = d_1031___mcc_h2_
                        if ((len((d_1032_args_)[0])) >= (1)) and (Int.default__.IsNatNumber((d_1032_args_)[0])):
                            return Int.default__.StringToNat((d_1032_args_)[0], 0)
                        elif True:
                            return 0
                    elif True:
                        d_1033___mcc_h3_ = source71_.msg
                        return 0

                d_1030_cfgDepthOpt_ = lambda72_((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1022_optArgs_))
                d_1034_rawOpt_: bool
                d_1034_rawOpt_ = (True if ((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_1022_optArgs_)).is_Success else False)
                d_1035_noTable_: bool
                d_1035_noTable_ = (True if ((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), d_1022_optArgs_)).is_Success else False)
                d_1036_info_: bool
                d_1036_info_ = (True if ((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--info")), d_1022_optArgs_)).is_Success else False)
                d_1037_fancy_: bool
                d_1037_fancy_ = (True if ((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_1022_optArgs_)).is_Success else False)
                d_1038_name_: _dafny.Seq
                def lambda73_(source72_):
                    if source72_.is_Success:
                        d_1039___mcc_h4_ = source72_.v
                        d_1040_args_ = d_1039___mcc_h4_
                        return (d_1040_args_)[0]
                    elif True:
                        d_1041___mcc_h5_ = source72_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Name not set"))

                d_1038_name_ = lambda73_((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--title")), d_1022_optArgs_))
                if d_1023_disOpt_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassembled code:\n"))).VerbatimString(False))
                    PrettyPrinters.default__.PrintInstructions(d_1021_x_)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
                d_1042_y_: _dafny.Seq
                d_1042_y_ = Splitter.default__.SplitUpToTerminal(d_1021_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_1043_prog_: EVMObject.EVMObj
                d_1043_prog_ = EVMObject.EVMObj_EVMObj(d_1042_y_, EVMObject.default__.CollectJumpDests(d_1042_y_), EVMObject.default__.CollectThem(d_1042_y_))
                if d_1036_info_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- Program Stats ---------\n"))).VerbatimString(False))
                    (d_1043_prog_).PrintByteCodeInfo()
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- End Program Stats ---------\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- Segment Stats ---------\n"))).VerbatimString(False))
                    (d_1043_prog_).PrintSegmentInfo()
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- End Segment Stats ---------\n"))).VerbatimString(False))
                if d_1024_segmentOpt_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                    PrettyPrinters.default__.PrintSegments(d_1042_y_, 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Segments -------------------\n"))).VerbatimString(False))
                if d_1025_proofOpt_:
                    d_1044_z_: _dafny.Seq
                    d_1044_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1042_y_)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Dafny Proof Object:\n"))).VerbatimString(False))
                    PrettyPrinters.default__.PrintProofObjectToDafny(d_1044_z_, d_1026_libOpt_)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Proof -------------------\n"))).VerbatimString(False))
                if (((d_1030_cfgDepthOpt_) > (0)) and ((len(d_1042_y_)) > (0))) and ((((d_1042_y_)[0]).StartAddress()) == (0)):
                    if d_1034_rawOpt_:
                        d_1045_a1_: Automata.Auto
                        d_1046_s1_: Statistics.Stats
                        out6_: Automata.Auto
                        out7_: Statistics.Stats
                        out6_, out7_ = (d_1043_prog_).BuildCFG(d_1030_cfgDepthOpt_, False)
                        d_1045_a1_ = out6_
                        d_1046_s1_ = out7_
                        d_1047_k_: _dafny.Seq
                        def lambda74_(d_1048_prog_, d_1049_a1_):
                            def lambda75_(d_1050_s_):
                                return (((d_1050_s_).is_EGState) and ((d_1050_s_).IsBounded(len((d_1048_prog_).xs)))) and ((((d_1048_prog_).xs)[(d_1050_s_).segNum]).is_INVALIDSeg)

                            return lambda75_

                        d_1047_k_ = MiscTypes.default__.Filter((d_1045_a1_).states, lambda74_(d_1043_prog_, d_1045_a1_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/*\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_1030_cfgDepthOpt_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print(((d_1046_s1_).PrettyPrint()).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of reachable invalid segments is: "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(len(d_1047_k_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of CFG: "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((d_1045_a1_).SSize()))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((d_1045_a1_).TSize(0)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "*/\n"))).VerbatimString(False))
                        def lambda76_(d_1051_prog_, d_1052_noTable_, d_1053_a1_):
                            def lambda77_(d_1054_s_):
                                return (d_1051_prog_).ToHTML(d_1054_s_, not(d_1052_noTable_))

                            return lambda77_

                        def lambda78_(d_1055_prog_, d_1056_a1_):
                            def lambda79_(d_1057_s_, d_1058_l_, d_1059___v3_):
                                return (d_1055_prog_).DotLabel(d_1057_s_, d_1058_l_)

                            return lambda79_

                        (d_1045_a1_).ToDot(lambda76_(d_1043_prog_, d_1035_noTable_, d_1045_a1_), lambda78_(d_1043_prog_, d_1045_a1_), ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "graph[labelloc=\"t\", labeljust=\"l\", label=<"))) + (default__.MakeTitle(d_1038_name_, (d_1045_a1_).SSize(), (d_1045_a1_).TSize(0), d_1030_cfgDepthOpt_, (d_1046_s1_).maxDepthReached))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "node [shape=none, fontname=arial, style=\"rounded, filled\", fillcolor= \"whitesmoke\"]\nedge [fontname=arial]\nranking=TB"))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "G")))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Raw CFG -------------------\n"))).VerbatimString(False))
                    elif True:
                        d_1060_a1_: Automata.Auto
                        d_1061_s1_: Statistics.Stats
                        out8_: Automata.Auto
                        out9_: Statistics.Stats
                        out8_, out9_ = (d_1043_prog_).BuildCFG(d_1030_cfgDepthOpt_, True)
                        d_1060_a1_ = out8_
                        d_1061_s1_ = out9_
                        d_1062_k_: _dafny.Seq
                        def lambda80_(d_1063_prog_, d_1064_a1_):
                            def lambda81_(d_1065_s_):
                                return (((d_1065_s_).is_EGState) and ((d_1065_s_).IsBounded(len((d_1063_prog_).xs)))) and ((((d_1063_prog_).xs)[(d_1065_s_).segNum]).is_INVALIDSeg)

                            return lambda81_

                        d_1062_k_ = MiscTypes.default__.Filter((d_1060_a1_).states, lambda80_(d_1043_prog_, d_1060_a1_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "/*\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(d_1030_cfgDepthOpt_))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print(((d_1061_s1_).PrettyPrint()).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of reachable invalid segments is: "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(len(d_1062_k_)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of non minimised CFG: "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(((d_1061_s1_).nonMinimisedSize)[0]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of(((d_1061_s1_).nonMinimisedSize)[1]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of minimised CFG: "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((d_1060_a1_).SSize()))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes, "))).VerbatimString(False))
                        _dafny.print(_dafny.string_of((d_1060_a1_).TSize(0)))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "*/\n"))).VerbatimString(False))
                        def lambda82_(d_1066_prog_, d_1067_noTable_, d_1068_a1_):
                            def lambda83_(d_1069_s_):
                                return (d_1066_prog_).ToHTML(d_1069_s_, not(d_1067_noTable_))

                            return lambda83_

                        def lambda84_(d_1070_prog_, d_1071_a1_):
                            def lambda85_(d_1072_s_, d_1073_l_, d_1074___v4_):
                                return (d_1070_prog_).DotLabel(d_1072_s_, d_1073_l_)

                            return lambda85_

                        (d_1060_a1_).ToDot(lambda82_(d_1043_prog_, d_1035_noTable_, d_1060_a1_), lambda84_(d_1043_prog_, d_1060_a1_), (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "graph[labelloc=\"t\", labeljust=\"l\", fontname=\"Arial\", label=<"))) + (default__.MakeTitle(d_1038_name_, (d_1060_a1_).SSize(), (d_1060_a1_).TSize(0), d_1030_cfgDepthOpt_, (d_1061_s1_).maxDepthReached))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "node [shape=none, fontname=arial, style=\"rounded, filled\", fillcolor= \"whitesmoke\"]\nedge [fontname=arial]\nranking=TB"))), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "G")))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "//----------------- Minimised CFG -------------------\n"))).VerbatimString(False))
                elif True:
                    if ((d_1018_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1022_optArgs_)).is_Success:
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found or --cfg argument is 0 or segment 0 does not start at pc=0\n"))).VerbatimString(False))

    @staticmethod
    def MakeTitle(name, numNodes, numEdges, maxDepth, reached):
        return (((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Program Name: </B> "))) + (name)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"left\"/>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Control Flow Graph Info: </B><BR ALIGN=\"left\"/>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth: ")))) + (Int.default__.NatToString(maxDepth))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Was reached")) if reached else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Was not reached"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"left\"/>")))) + (Int.default__.NatToString(numNodes))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " nodes/")))) + (Int.default__.NatToString(numEdges))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " edges<BR ALIGN=\"left\"/>")))

