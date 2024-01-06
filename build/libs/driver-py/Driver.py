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
import CFGObject

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_1048_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_1048_optionParser_ = nw1_
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows.")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-n")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-t")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--title")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The name of the program.")))
        (d_1048_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-i")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--info")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The stats of the program (size, segments).")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_1048_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            if (len((args)[1])) == (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty \n"))).VerbatimString(False))
            elif (_dafny.euclidian_modulus(len((args)[1]), 2)) != (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty and have even length, length is "))).VerbatimString(False))
                _dafny.print(_dafny.string_of(len((args)[1])))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            elif Hex.default__.IsHexString((_dafny.SeqWithoutIsStrInference(((args)[1])[2::]) if (_dafny.SeqWithoutIsStrInference(((args)[1])[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else (args)[1])):
                d_1049_x_: _dafny.Seq
                d_1049_x_ = BinaryDecoder.default__.Disassemble((_dafny.SeqWithoutIsStrInference(((args)[1])[2::]) if (_dafny.SeqWithoutIsStrInference(((args)[1])[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else (args)[1]), _dafny.SeqWithoutIsStrInference([]), 0)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassembled code:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintInstructions(d_1049_x_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
            elif True:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be hexadecimal\n"))).VerbatimString(False))
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_1048_optionParser_).PrintHelp()
        elif True:
            d_1050_stringToProcess_: _dafny.Seq
            d_1050_stringToProcess_ = (args)[(len(args)) - (1)]
            if (len(d_1050_stringToProcess_)) == (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty \n"))).VerbatimString(False))
            elif (_dafny.euclidian_modulus(len(d_1050_stringToProcess_), 2)) != (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must have even length, length is "))).VerbatimString(False))
                _dafny.print(_dafny.string_of(len(d_1050_stringToProcess_)))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            elif not(Hex.default__.IsHexString((_dafny.SeqWithoutIsStrInference((d_1050_stringToProcess_)[2::]) if (_dafny.SeqWithoutIsStrInference((d_1050_stringToProcess_)[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else d_1050_stringToProcess_))):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be hexadecimal\n"))).VerbatimString(False))
            elif True:
                d_1051_x_: _dafny.Seq
                d_1051_x_ = BinaryDecoder.default__.Disassemble((_dafny.SeqWithoutIsStrInference((d_1050_stringToProcess_)[2::]) if (_dafny.SeqWithoutIsStrInference((d_1050_stringToProcess_)[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else d_1050_stringToProcess_), _dafny.SeqWithoutIsStrInference([]), 0)
                d_1052_optArgs_: _dafny.Seq
                d_1052_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
                d_1053_disOpt_: bool
                d_1053_disOpt_ = (True if ((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_1052_optArgs_)).is_Success else False)
                d_1054_segmentOpt_: bool
                d_1054_segmentOpt_ = (True if ((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_1052_optArgs_)).is_Success else False)
                d_1055_proofOpt_: bool
                d_1055_proofOpt_ = (True if ((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_1052_optArgs_)).is_Success else False)
                d_1056_libOpt_: _dafny.Seq
                def lambda80_(source71_):
                    if source71_.is_Success:
                        d_1057___mcc_h0_ = source71_.v
                        d_1058_p_ = d_1057___mcc_h0_
                        return (d_1058_p_)[0]
                    elif True:
                        d_1059___mcc_h1_ = source71_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_1056_libOpt_ = lambda80_((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_1052_optArgs_))
                d_1060_cfgDepthOpt_: int
                def lambda81_(source72_):
                    if source72_.is_Success:
                        d_1061___mcc_h2_ = source72_.v
                        d_1062_args_ = d_1061___mcc_h2_
                        if ((len((d_1062_args_)[0])) >= (1)) and (Int.default__.IsNatNumber((d_1062_args_)[0])):
                            return Int.default__.StringToNat((d_1062_args_)[0], 0)
                        elif True:
                            return 0
                    elif True:
                        d_1063___mcc_h3_ = source72_.msg
                        return 0

                d_1060_cfgDepthOpt_ = lambda81_((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_1052_optArgs_))
                d_1064_rawOpt_: bool
                d_1064_rawOpt_ = (True if ((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_1052_optArgs_)).is_Success else False)
                d_1065_noTable_: bool
                d_1065_noTable_ = (True if ((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), d_1052_optArgs_)).is_Success else False)
                d_1066_info_: bool
                d_1066_info_ = (True if ((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--info")), d_1052_optArgs_)).is_Success else False)
                d_1067_fancy_: bool
                d_1067_fancy_ = (True if ((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_1052_optArgs_)).is_Success else False)
                d_1068_name_: _dafny.Seq
                def lambda82_(source73_):
                    if source73_.is_Success:
                        d_1069___mcc_h4_ = source73_.v
                        d_1070_args_ = d_1069___mcc_h4_
                        return (d_1070_args_)[0]
                    elif True:
                        d_1071___mcc_h5_ = source73_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Name not set"))

                d_1068_name_ = lambda82_((d_1048_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--title")), d_1052_optArgs_))
                if d_1053_disOpt_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassembled code:\n"))).VerbatimString(False))
                    PrettyPrinters.default__.PrintInstructions(d_1051_x_)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
                d_1072_y_: _dafny.Seq
                d_1072_y_ = Splitter.default__.SplitUpToTerminal(d_1051_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_1073_prog_: EVMObject.EVMObj
                d_1073_prog_ = EVMObject.EVMObj_EVMObj(d_1072_y_, EVMObject.default__.CollectJumpDests(d_1072_y_), EVMObject.default__.CollectThem(d_1072_y_))
                if d_1066_info_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- Program Stats ---------\n"))).VerbatimString(False))
                    (d_1073_prog_).PrintByteCodeInfo()
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- End Program Stats ---------\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- Segment Stats ---------\n"))).VerbatimString(False))
                    (d_1073_prog_).PrintSegmentInfo()
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- End Segment Stats ---------\n"))).VerbatimString(False))
                if d_1054_segmentOpt_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                    PrettyPrinters.default__.PrintSegments(d_1072_y_, 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Segments -------------------\n"))).VerbatimString(False))
                if d_1055_proofOpt_:
                    d_1074_z_: _dafny.Seq
                    d_1074_z_ = ProofObjectBuilder.default__.BuildProofObject(d_1072_y_)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Dafny Proof Object:\n"))).VerbatimString(False))
                    PrettyPrinters.default__.PrintProofObjectToDafny(d_1074_z_, d_1056_libOpt_)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Proof -------------------\n"))).VerbatimString(False))
                if (((d_1060_cfgDepthOpt_) > (0)) and ((len(d_1072_y_)) > (0))) and ((((d_1072_y_)[0]).StartAddress()) == (0)):
                    d_1075_a1_: Automata.Auto
                    d_1076_s1_: Statistics.Stats
                    out6_: Automata.Auto
                    out7_: Statistics.Stats
                    out6_, out7_ = (d_1073_prog_).BuildCFG(d_1060_cfgDepthOpt_, not(d_1064_rawOpt_))
                    d_1075_a1_ = out6_
                    d_1076_s1_ = out7_
                    d_1077_cfgObj_: CFGObject.CFGObj
                    d_1077_cfgObj_ = CFGObject.CFGObj_CFGObj(d_1073_prog_, d_1060_cfgDepthOpt_, d_1075_a1_, not(d_1064_rawOpt_), d_1076_s1_)
                    (d_1077_cfgObj_).ToDot(d_1065_noTable_, d_1068_name_)

