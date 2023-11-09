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
import State
import WeakPre
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
import CFGraph
import BuildCFGraph

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_616_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_616_optionParser_ = nw1_
        (d_616_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_616_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_616_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_616_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_616_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_616_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_616_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_617_x_: _dafny.Seq
            d_617_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_617_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_616_optionParser_).PrintHelp()
        elif True:
            d_618_stringToProcess_: _dafny.Seq
            d_618_stringToProcess_ = (args)[(len(args)) - (1)]
            d_619_optArgs_: _dafny.Seq
            d_619_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_620_x_: _dafny.Seq
            d_620_x_ = BinaryDecoder.default__.Disassemble(d_618_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source49_ = (d_616_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_619_optArgs_)
            if source49_.is_Success:
                d_621___mcc_h0_ = source49_.v
                PrettyPrinters.default__.PrintInstructions(d_620_x_)
            elif True:
                d_622___mcc_h1_ = source49_.msg
                pass
            source50_ = (d_616_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_619_optArgs_)
            if source50_.is_Success:
                d_623___mcc_h2_ = source50_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_624_y_: _dafny.Seq
                d_624_y_ = Splitter.default__.SplitUpToTerminal(d_620_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_624_y_, 0)
            elif True:
                d_625___mcc_h3_ = source50_.msg
                pass
            source51_ = (d_616_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_619_optArgs_)
            if source51_.is_Success:
                d_626___mcc_h4_ = source51_.v
                d_627_pathToDafnyLib_: _dafny.Seq
                def lambda18_(source52_):
                    if source52_.is_Success:
                        d_628___mcc_h6_ = source52_.v
                        def iife22_(_pat_let11_0):
                            def iife23_(d_629_p_):
                                return (d_629_p_)[0]
                            return iife23_(_pat_let11_0)
                        return iife22_(d_628___mcc_h6_)
                    elif True:
                        d_630___mcc_h7_ = source52_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_627_pathToDafnyLib_ = lambda18_((d_616_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_619_optArgs_))
                d_631_y_: _dafny.Seq
                d_631_y_ = Splitter.default__.SplitUpToTerminal(d_620_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_632_z_: _dafny.Seq
                d_632_z_ = ProofObjectBuilder.default__.BuildProofObject(d_631_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_632_z_, d_627_pathToDafnyLib_)
            elif True:
                d_633___mcc_h5_ = source51_.msg
                pass
            source53_ = (d_616_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_619_optArgs_)
            if source53_.is_Success:
                d_634___mcc_h8_ = source53_.v
                PrettyPrinters.default__.PrintInstructions(d_620_x_)
                d_635_pathToDafnyLib_: _dafny.Seq
                def lambda19_(source54_):
                    if source54_.is_Success:
                        d_636___mcc_h10_ = source54_.v
                        def iife24_(_pat_let12_0):
                            def iife25_(d_637_p_):
                                return (d_637_p_)[0]
                            return iife25_(_pat_let12_0)
                        return iife24_(d_636___mcc_h10_)
                    elif True:
                        d_638___mcc_h11_ = source54_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_635_pathToDafnyLib_ = lambda19_((d_616_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_619_optArgs_))
                d_639_y_: _dafny.Seq
                d_639_y_ = Splitter.default__.SplitUpToTerminal(d_620_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_640_z_: _dafny.Seq
                d_640_z_ = ProofObjectBuilder.default__.BuildProofObject(d_639_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_640_z_, d_635_pathToDafnyLib_)
            elif True:
                d_641___mcc_h9_ = source53_.msg
                pass
            source55_ = (d_616_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_619_optArgs_)
            if source55_.is_Success:
                d_642___mcc_h12_ = source55_.v
                d_643_m_ = d_642___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_644_y_: _dafny.Seq
                d_644_y_ = Splitter.default__.SplitUpToTerminal(d_620_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_644_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_643_m_)[0])) == (0)) or (not(default__.IsNatNumber((d_643_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_645_maxDepth_: int
                    d_645_maxDepth_ = default__.StringToNat((d_643_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_645_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_646_r_: _dafny.Seq
                    d_646_r_ = BuildCFGraph.default__.BuildCFGV4(d_644_y_, d_645_maxDepth_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG test 1\n"))).VerbatimString(False))
                    _dafny.print((CFGraph.BoolCFGraph.DOTPrint(d_646_r_, d_644_y_)).VerbatimString(False))
            elif True:
                d_647___mcc_h13_ = source55_.msg
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
                    source56_ = default__.CharToDigit((s)[0])
                    if source56_.is_None:
                        return False
                    elif True:
                        d_648___mcc_h0_ = source56_.v
                        d_649_v_ = d_648___mcc_h0_
                        in77_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        s = in77_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_650_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_650_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

