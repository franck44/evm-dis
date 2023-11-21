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
import WeakPre
import State
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
        d_812_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_812_optionParser_ = nw1_
        (d_812_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_812_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_812_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_812_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_812_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_812_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_812_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_812_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_813_x_: _dafny.Seq
            d_813_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_813_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_812_optionParser_).PrintHelp()
        elif True:
            d_814_stringToProcess_: _dafny.Seq
            d_814_stringToProcess_ = (args)[(len(args)) - (1)]
            d_815_optArgs_: _dafny.Seq
            d_815_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_816_x_: _dafny.Seq
            d_816_x_ = BinaryDecoder.default__.Disassemble(d_814_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source67_ = (d_812_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_815_optArgs_)
            if source67_.is_Success:
                d_817___mcc_h0_ = source67_.v
                PrettyPrinters.default__.PrintInstructions(d_816_x_)
            elif True:
                d_818___mcc_h1_ = source67_.msg
                pass
            source68_ = (d_812_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_815_optArgs_)
            if source68_.is_Success:
                d_819___mcc_h2_ = source68_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_820_y_: _dafny.Seq
                d_820_y_ = Splitter.default__.SplitUpToTerminal(d_816_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_820_y_, 0)
            elif True:
                d_821___mcc_h3_ = source68_.msg
                pass
            source69_ = (d_812_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_815_optArgs_)
            if source69_.is_Success:
                d_822___mcc_h4_ = source69_.v
                d_823_pathToDafnyLib_: _dafny.Seq
                def lambda41_(source70_):
                    if source70_.is_Success:
                        d_824___mcc_h6_ = source70_.v
                        def iife45_(_pat_let22_0):
                            def iife46_(d_825_p_):
                                return (d_825_p_)[0]
                            return iife46_(_pat_let22_0)
                        return iife45_(d_824___mcc_h6_)
                    elif True:
                        d_826___mcc_h7_ = source70_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_823_pathToDafnyLib_ = lambda41_((d_812_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_815_optArgs_))
                d_827_y_: _dafny.Seq
                d_827_y_ = Splitter.default__.SplitUpToTerminal(d_816_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_828_z_: _dafny.Seq
                d_828_z_ = ProofObjectBuilder.default__.BuildProofObject(d_827_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_828_z_, d_823_pathToDafnyLib_)
            elif True:
                d_829___mcc_h5_ = source69_.msg
                pass
            source71_ = (d_812_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_815_optArgs_)
            if source71_.is_Success:
                d_830___mcc_h8_ = source71_.v
                PrettyPrinters.default__.PrintInstructions(d_816_x_)
                d_831_pathToDafnyLib_: _dafny.Seq
                def lambda42_(source72_):
                    if source72_.is_Success:
                        d_832___mcc_h10_ = source72_.v
                        def iife47_(_pat_let23_0):
                            def iife48_(d_833_p_):
                                return (d_833_p_)[0]
                            return iife48_(_pat_let23_0)
                        return iife47_(d_832___mcc_h10_)
                    elif True:
                        d_834___mcc_h11_ = source72_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_831_pathToDafnyLib_ = lambda42_((d_812_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_815_optArgs_))
                d_835_y_: _dafny.Seq
                d_835_y_ = Splitter.default__.SplitUpToTerminal(d_816_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_836_z_: _dafny.Seq
                d_836_z_ = ProofObjectBuilder.default__.BuildProofObject(d_835_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_836_z_, d_831_pathToDafnyLib_)
            elif True:
                d_837___mcc_h9_ = source71_.msg
                pass
            source73_ = (d_812_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_815_optArgs_)
            if source73_.is_Success:
                d_838___mcc_h12_ = source73_.v
                d_839_m_ = d_838___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_840_y_: _dafny.Seq
                d_840_y_ = Splitter.default__.SplitUpToTerminal(d_816_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_840_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_839_m_)[0])) == (0)) or (not(default__.IsNatNumber((d_839_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_841_maxDepth_: int
                    d_841_maxDepth_ = default__.StringToNat((d_839_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_841_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_842_startAddress_: int
                    d_842_startAddress_ = ((d_840_y_)[0]).StartAddress()
                    pat_let_tv47_ = d_842_startAddress_
                    d_843_startState_: State.AState
                    def iife49_(_pat_let24_0):
                        def iife50_(d_844_dt__update__tmp_h0_):
                            def iife51_(_pat_let25_0):
                                def iife52_(d_845_dt__update_hpc_h0_):
                                    return State.AState_EState(d_845_dt__update_hpc_h0_, (d_844_dt__update__tmp_h0_).stack)
                                return iife52_(_pat_let25_0)
                            return iife51_(pat_let_tv47_)
                        return iife50_(_pat_let24_0)
                    d_843_startState_ = iife49_(State.default__.DEFAULT__VALIDSTATE)
                    if (((d_840_y_)[0]).StartAddress()) != (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment 0 does not start at address 0.\n"))).VerbatimString(False))
                    elif True:
                        d_846_g_: CFGraph.BoolCFGraph
                        d_846_g_ = BuildCFGraph.default__.BuildCFGV4(d_840_y_, d_841_maxDepth_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]))
                        if ((d_812_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_815_optArgs_)).is_Success:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_846_g_).DOTPrint(d_840_y_)).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Computing Minimised CFG\n"))).VerbatimString(False))
                        d_847_g_k_: CFGraph.BoolCFGraph
                        d_847_g_k_ = (d_846_g_).Minimise()
                        if not((d_847_g_k_).IsValid()):
                            raise _dafny.HaltException("src/dafny/Driver.dfy(138,14): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                        _dafny.print(((d_847_g_k_).DOTPrint(d_840_y_)).VerbatimString(False))
            elif True:
                d_848___mcc_h13_ = source73_.msg
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
                    source74_ = default__.CharToDigit((s)[0])
                    if source74_.is_None:
                        return False
                    elif True:
                        d_849___mcc_h0_ = source74_.v
                        d_850_v_ = d_849___mcc_h0_
                        in142_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        s = in142_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_851_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_851_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

