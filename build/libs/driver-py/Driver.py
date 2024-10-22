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
import HTML as HTML
import EVMObject as EVMObject
import ArgParser as ArgParser
import CFGObject as CFGObject

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_0_optionParser_: ArgParser.ArgumentParser
        nw0_ = ArgParser.ArgumentParser()
        nw0_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_0_optionParser_ = nw0_
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object to verify/use the CFG for <string>")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-e")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--refine")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object with distinct segments <string>")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-z")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--size")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The max size of segments. Default is upto terminal instructions or JUMPDEST.")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-n")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Don't use tables to pretty-print DOT file. Reduces size of the DOT file.")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-t")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--title")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The name of the program.")))
        (d_0_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-i")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--info")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The stats of the program (size, segments).")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_0_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            if (len((args)[1])) == (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty \n"))).VerbatimString(False))
            elif (_dafny.euclidian_modulus(len((args)[1]), 2)) != (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty and have even length, length is "))).VerbatimString(False))
                _dafny.print(_dafny.string_of(len((args)[1])))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            elif Hex.default__.IsHexString((_dafny.SeqWithoutIsStrInference(((args)[1])[2::]) if (_dafny.SeqWithoutIsStrInference(((args)[1])[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else (args)[1])):
                d_1_x_: _dafny.Seq
                d_1_x_ = BinaryDecoder.default__.Disassemble((_dafny.SeqWithoutIsStrInference(((args)[1])[2::]) if (_dafny.SeqWithoutIsStrInference(((args)[1])[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else (args)[1]), _dafny.SeqWithoutIsStrInference([]), 0)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassembled code:\n"))).VerbatimString(False))
                PrettyPrinters.default__.PrintInstructions(d_1_x_)
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
            elif True:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be hexadecimal\n"))).VerbatimString(False))
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_0_optionParser_).PrintHelp()
        elif True:
            d_2_stringToProcess_: _dafny.Seq
            d_2_stringToProcess_ = (args)[(len(args)) - (1)]
            if (len(d_2_stringToProcess_)) == (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be non empty \n"))).VerbatimString(False))
            elif (_dafny.euclidian_modulus(len(d_2_stringToProcess_), 2)) != (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must have even length, length is "))).VerbatimString(False))
                _dafny.print(_dafny.string_of(len(d_2_stringToProcess_)))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            elif not(Hex.default__.IsHexString((_dafny.SeqWithoutIsStrInference((d_2_stringToProcess_)[2::]) if (_dafny.SeqWithoutIsStrInference((d_2_stringToProcess_)[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else d_2_stringToProcess_))):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must be hexadecimal\n"))).VerbatimString(False))
            elif True:
                d_3_x_: _dafny.Seq
                d_3_x_ = BinaryDecoder.default__.Disassemble((_dafny.SeqWithoutIsStrInference((d_2_stringToProcess_)[2::]) if (_dafny.SeqWithoutIsStrInference((d_2_stringToProcess_)[:2:])) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) else d_2_stringToProcess_), _dafny.SeqWithoutIsStrInference([]), 0)
                d_4_optArgs_: _dafny.Seq
                d_4_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
                d_5_disOpt_: bool
                if ((d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_4_optArgs_)).is_Success:
                    d_5_disOpt_ = True
                elif True:
                    d_5_disOpt_ = False
                d_6_segmentOpt_: bool
                if ((d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_4_optArgs_)).is_Success:
                    d_6_segmentOpt_ = True
                elif True:
                    d_6_segmentOpt_ = False
                d_7_proofOpt_: bool
                if ((d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_4_optArgs_)).is_Success:
                    d_7_proofOpt_ = True
                elif True:
                    d_7_proofOpt_ = False
                d_8_proofRefine_: bool
                if ((d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--refine")), d_4_optArgs_)).is_Success:
                    d_8_proofRefine_ = True
                elif True:
                    d_8_proofRefine_ = False
                d_9_libOpt_: _dafny.Seq
                source0_ = (d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_4_optArgs_)
                with _dafny.label("match0"):
                    if True:
                        if source0_.is_Success:
                            d_10_p_ = source0_.v
                            d_9_libOpt_ = (d_10_p_)[0]
                            raise _dafny.Break("match0")
                    if True:
                        d_9_libOpt_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
                    pass
                d_11_cfgDepthOpt_: int
                source1_ = (d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_4_optArgs_)
                with _dafny.label("match1"):
                    if True:
                        if source1_.is_Success:
                            d_12_args_ = source1_.v
                            if ((len((d_12_args_)[0])) >= (1)) and (Int.default__.IsNatNumber((d_12_args_)[0])):
                                d_11_cfgDepthOpt_ = Int.default__.StringToNat((d_12_args_)[0], 0)
                            elif True:
                                d_11_cfgDepthOpt_ = 0
                            raise _dafny.Break("match1")
                    if True:
                        d_11_cfgDepthOpt_ = 0
                    pass
                d_13_rawOpt_: bool
                if ((d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_4_optArgs_)).is_Success:
                    d_13_rawOpt_ = True
                elif True:
                    d_13_rawOpt_ = False
                d_14_noTable_: bool
                if ((d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--notable")), d_4_optArgs_)).is_Success:
                    d_14_noTable_ = True
                elif True:
                    d_14_noTable_ = False
                d_15_info_: bool
                if ((d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--info")), d_4_optArgs_)).is_Success:
                    d_15_info_ = True
                elif True:
                    d_15_info_ = False
                d_16_maxSegSize_: MiscTypes.Option
                source2_ = (d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--size")), d_4_optArgs_)
                with _dafny.label("match2"):
                    if True:
                        if source2_.is_Success:
                            d_17_args_ = source2_.v
                            if ((len((d_17_args_)[0])) >= (1)) and (Int.default__.IsNatNumber((d_17_args_)[0])):
                                d_16_maxSegSize_ = MiscTypes.Option_Some(Int.default__.StringToNat((d_17_args_)[0], 0))
                            elif True:
                                d_16_maxSegSize_ = MiscTypes.Option_None()
                            raise _dafny.Break("match2")
                    if True:
                        d_16_maxSegSize_ = MiscTypes.Option_None()
                    pass
                d_18_name_: _dafny.Seq
                source3_ = (d_0_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--title")), d_4_optArgs_)
                with _dafny.label("match3"):
                    if True:
                        if source3_.is_Success:
                            d_19_args_ = source3_.v
                            d_18_name_ = (d_19_args_)[0]
                            raise _dafny.Break("match3")
                    if True:
                        d_18_name_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Name not set"))
                    pass
                if d_5_disOpt_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassembled code:\n"))).VerbatimString(False))
                    PrettyPrinters.default__.PrintInstructions(d_3_x_)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--------------- Disassembled ---------------------\n"))).VerbatimString(False))
                d_20_y_: _dafny.Seq
                d_20_y_ = Splitter.default__.SplitUpToTerminal(d_3_x_, d_16_maxSegSize_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_21_prog_: EVMObject.EVMObj
                d_21_prog_ = EVMObject.EVMObj_EVMObj(d_20_y_, EVMObject.default__.CollectJumpDests(d_20_y_), EVMObject.default__.CollectThem(d_20_y_))
                if d_15_info_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- Program Stats ---------\n"))).VerbatimString(False))
                    (d_21_prog_).PrintByteCodeInfo()
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- End Program Stats ---------\n"))).VerbatimString(False))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- Segment Stats ---------\n"))).VerbatimString(False))
                    (d_21_prog_).PrintSegmentInfo()
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-------- End Segment Stats ---------\n"))).VerbatimString(False))
                if d_6_segmentOpt_:
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                    PrettyPrinters.default__.PrintSegments(d_20_y_, 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "----------------- Segments -------------------\n"))).VerbatimString(False))
                if (((d_11_cfgDepthOpt_) > (0)) and ((len(d_20_y_)) > (0))) and ((((d_20_y_)[0]).StartAddress()) == (0)):
                    d_22_a1_: Automata.Auto
                    d_23_s1_: Statistics.Stats
                    out0_: Automata.Auto
                    out1_: Statistics.Stats
                    out0_, out1_ = (d_21_prog_).BuildCFG(d_11_cfgDepthOpt_, not(d_13_rawOpt_))
                    d_22_a1_ = out0_
                    d_23_s1_ = out1_
                    d_24_cfgObj_: CFGObject.CFGObj
                    d_24_cfgObj_ = CFGObject.CFGObj_CFGObj(d_21_prog_, d_11_cfgDepthOpt_, d_22_a1_, not(d_13_rawOpt_), d_23_s1_)
                    if d_7_proofOpt_:
                        if (d_24_cfgObj_).HasNoErrorState():
                            (d_24_cfgObj_).CFGCheckerToDafny(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EVMProofObject")), d_9_libOpt_)
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The CFG has some error states and the Dafny proof object cannot be generated\n"))).VerbatimString(False))
                    elif d_8_proofRefine_:
                        if (d_24_cfgObj_).HasNoErrorState():
                            (d_24_cfgObj_).CFGRefineToDafny(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EVMProofObject")), d_9_libOpt_)
                        elif True:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The CFG has some error states and the Dafny proof object cannot be generated\n"))).VerbatimString(False))
                    elif True:
                        (d_24_cfgObj_).ToDot(d_14_noTable_, d_18_name_)

