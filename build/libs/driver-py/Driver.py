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
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph
import BuildCFGraph

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_764_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_764_optionParser_ = nw1_
        (d_764_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_764_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_764_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_764_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_764_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_764_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_764_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_765_x_: _dafny.Seq
            d_765_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_765_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_764_optionParser_).PrintHelp()
        elif True:
            d_766_stringToProcess_: _dafny.Seq
            d_766_stringToProcess_ = (args)[(len(args)) - (1)]
            d_767_optArgs_: _dafny.Seq
            d_767_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_768_x_: _dafny.Seq
            d_768_x_ = BinaryDecoder.default__.Disassemble(d_766_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source61_ = (d_764_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_767_optArgs_)
            if source61_.is_Success:
                d_769___mcc_h0_ = source61_.v
                PrettyPrinters.default__.PrintInstructions(d_768_x_)
            elif True:
                d_770___mcc_h1_ = source61_.msg
                pass
            source62_ = (d_764_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_767_optArgs_)
            if source62_.is_Success:
                d_771___mcc_h2_ = source62_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_772_y_: _dafny.Seq
                d_772_y_ = Splitter.default__.SplitUpToTerminal(d_768_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_772_y_, 0)
            elif True:
                d_773___mcc_h3_ = source62_.msg
                pass
            source63_ = (d_764_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_767_optArgs_)
            if source63_.is_Success:
                d_774___mcc_h4_ = source63_.v
                d_775_pathToDafnyLib_: _dafny.Seq
                def lambda43_(source64_):
                    if source64_.is_Success:
                        d_776___mcc_h6_ = source64_.v
                        def iife51_(_pat_let25_0):
                            def iife52_(d_777_p_):
                                return (d_777_p_)[0]
                            return iife52_(_pat_let25_0)
                        return iife51_(d_776___mcc_h6_)
                    elif True:
                        d_778___mcc_h7_ = source64_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_775_pathToDafnyLib_ = lambda43_((d_764_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_767_optArgs_))
                d_779_y_: _dafny.Seq
                d_779_y_ = Splitter.default__.SplitUpToTerminal(d_768_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_780_z_: _dafny.Seq
                d_780_z_ = ProofObjectBuilder.default__.BuildProofObject(d_779_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_780_z_, d_775_pathToDafnyLib_)
            elif True:
                d_781___mcc_h5_ = source63_.msg
                pass
            source65_ = (d_764_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_767_optArgs_)
            if source65_.is_Success:
                d_782___mcc_h8_ = source65_.v
                PrettyPrinters.default__.PrintInstructions(d_768_x_)
                d_783_pathToDafnyLib_: _dafny.Seq
                def lambda44_(source66_):
                    if source66_.is_Success:
                        d_784___mcc_h10_ = source66_.v
                        def iife53_(_pat_let26_0):
                            def iife54_(d_785_p_):
                                return (d_785_p_)[0]
                            return iife54_(_pat_let26_0)
                        return iife53_(d_784___mcc_h10_)
                    elif True:
                        d_786___mcc_h11_ = source66_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_783_pathToDafnyLib_ = lambda44_((d_764_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_767_optArgs_))
                d_787_y_: _dafny.Seq
                d_787_y_ = Splitter.default__.SplitUpToTerminal(d_768_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_788_z_: _dafny.Seq
                d_788_z_ = ProofObjectBuilder.default__.BuildProofObject(d_787_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_788_z_, d_783_pathToDafnyLib_)
            elif True:
                d_789___mcc_h9_ = source65_.msg
                pass
            source67_ = (d_764_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_767_optArgs_)
            if source67_.is_Success:
                d_790___mcc_h12_ = source67_.v
                d_791_m_ = d_790___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_792_y_: _dafny.Seq
                d_792_y_ = Splitter.default__.SplitUpToTerminal(d_768_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_792_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_791_m_)[0])) == (0)) or (not(default__.IsNatNumber((d_791_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_793_maxDepth_: int
                    d_793_maxDepth_ = default__.StringToNat((d_791_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_793_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_794_startAddress_: int
                    d_794_startAddress_ = ((d_792_y_)[0]).StartAddress()
                    pat_let_tv48_ = d_794_startAddress_
                    d_795_startState_: State.AState
                    def iife55_(_pat_let27_0):
                        def iife56_(d_796_dt__update__tmp_h0_):
                            def iife57_(_pat_let28_0):
                                def iife58_(d_797_dt__update_hpc_h0_):
                                    return State.AState_EState(d_797_dt__update_hpc_h0_, (d_796_dt__update__tmp_h0_).stack)
                                return iife58_(_pat_let28_0)
                            return iife57_(pat_let_tv48_)
                        return iife56_(_pat_let27_0)
                    d_795_startState_ = iife55_(State.default__.DEFAULT__VALIDSTATE)
                    if (((d_792_y_)[0]).StartAddress()) != (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment 0 does not start at address 0.\n"))).VerbatimString(False))
                    elif True:
                        d_798_g_: CFGraph.BoolCFGraph
                        d_798_g_ = BuildCFGraph.default__.BuildCFGV4(d_792_y_, d_793_maxDepth_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Computing Minimised CFG\n"))).VerbatimString(False))
                        d_799_g_k_: CFGraph.BoolCFGraph
                        d_799_g_k_ = (d_798_g_).Minimise()
                        if not((d_799_g_k_).IsValid()):
                            raise _dafny.HaltException("src/dafny/Driver.dfy(133,14): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                        _dafny.print(((d_799_g_k_).DOTPrint(d_792_y_)).VerbatimString(False))
            elif True:
                d_800___mcc_h13_ = source67_.msg
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
                    source68_ = default__.CharToDigit((s)[0])
                    if source68_.is_None:
                        return False
                    elif True:
                        d_801___mcc_h0_ = source68_.v
                        d_802_v_ = d_801___mcc_h0_
                        in124_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        s = in124_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_803_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_803_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

