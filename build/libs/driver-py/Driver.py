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

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_273_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_273_optionParser_ = nw1_
        (d_273_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_273_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_273_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_273_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_273_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_273_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_274_x_: _dafny.Seq
            d_274_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_274_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_273_optionParser_).PrintHelp()
        elif True:
            d_275_stringToProcess_: _dafny.Seq
            d_275_stringToProcess_ = (args)[(len(args)) - (1)]
            d_276_optArgs_: _dafny.Seq
            d_276_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_277_x_: _dafny.Seq
            d_277_x_ = BinaryDecoder.default__.Disassemble(d_275_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source16_ = (d_273_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_276_optArgs_)
            if source16_.is_Success:
                d_278___mcc_h0_ = source16_.v
                PrettyPrinters.default__.PrintInstructions(d_277_x_)
            elif True:
                d_279___mcc_h1_ = source16_.msg
                pass
            source17_ = (d_273_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_276_optArgs_)
            if source17_.is_Success:
                d_280___mcc_h2_ = source17_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_281_y_: _dafny.Seq
                d_281_y_ = Splitter.default__.SplitUpToTerminal(d_277_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_281_y_, 0)
            elif True:
                d_282___mcc_h3_ = source17_.msg
                pass
            source18_ = (d_273_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_276_optArgs_)
            if source18_.is_Success:
                d_283___mcc_h4_ = source18_.v
                d_284_pathToDafnyLib_: _dafny.Seq
                def lambda0_(source19_):
                    if source19_.is_Success:
                        d_285___mcc_h6_ = source19_.v
                        def iife2_(_pat_let1_0):
                            def iife3_(d_286_p_):
                                return (d_286_p_)[0]
                            return iife3_(_pat_let1_0)
                        return iife2_(d_285___mcc_h6_)
                    elif True:
                        d_287___mcc_h7_ = source19_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_284_pathToDafnyLib_ = lambda0_((d_273_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_276_optArgs_))
                d_288_y_: _dafny.Seq
                d_288_y_ = Splitter.default__.SplitUpToTerminal(d_277_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_289_z_: _dafny.Seq
                d_289_z_ = ProofObjectBuilder.default__.BuildProofObject(d_288_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_289_z_, d_284_pathToDafnyLib_)
            elif True:
                d_290___mcc_h5_ = source18_.msg
                pass
            source20_ = (d_273_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_276_optArgs_)
            if source20_.is_Success:
                d_291___mcc_h8_ = source20_.v
                PrettyPrinters.default__.PrintInstructions(d_277_x_)
                d_292_pathToDafnyLib_: _dafny.Seq
                def lambda1_(source21_):
                    if source21_.is_Success:
                        d_293___mcc_h10_ = source21_.v
                        def iife4_(_pat_let2_0):
                            def iife5_(d_294_p_):
                                return (d_294_p_)[0]
                            return iife5_(_pat_let2_0)
                        return iife4_(d_293___mcc_h10_)
                    elif True:
                        d_295___mcc_h11_ = source21_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_292_pathToDafnyLib_ = lambda1_((d_273_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_276_optArgs_))
                d_296_y_: _dafny.Seq
                d_296_y_ = Splitter.default__.SplitUpToTerminal(d_277_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_297_z_: _dafny.Seq
                d_297_z_ = ProofObjectBuilder.default__.BuildProofObject(d_296_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_297_z_, d_292_pathToDafnyLib_)
            elif True:
                d_298___mcc_h9_ = source20_.msg
                pass

