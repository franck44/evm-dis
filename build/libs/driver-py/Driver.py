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
import LoopResolver
import BuildCFGraph

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        d_795_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_795_optionParser_ = nw1_
        (d_795_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_795_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_795_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_795_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_795_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_795_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_795_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_795_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_796_x_: _dafny.Seq
            d_796_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_796_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_795_optionParser_).PrintHelp()
        elif True:
            d_797_stringToProcess_: _dafny.Seq
            d_797_stringToProcess_ = (args)[(len(args)) - (1)]
            d_798_optArgs_: _dafny.Seq
            d_798_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_799_x_: _dafny.Seq
            d_799_x_ = BinaryDecoder.default__.Disassemble(d_797_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source66_ = (d_795_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_798_optArgs_)
            if source66_.is_Success:
                d_800___mcc_h0_ = source66_.v
                PrettyPrinters.default__.PrintInstructions(d_799_x_)
            elif True:
                d_801___mcc_h1_ = source66_.msg
                pass
            source67_ = (d_795_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_798_optArgs_)
            if source67_.is_Success:
                d_802___mcc_h2_ = source67_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_803_y_: _dafny.Seq
                d_803_y_ = Splitter.default__.SplitUpToTerminal(d_799_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_803_y_, 0)
            elif True:
                d_804___mcc_h3_ = source67_.msg
                pass
            source68_ = (d_795_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_798_optArgs_)
            if source68_.is_Success:
                d_805___mcc_h4_ = source68_.v
                d_806_pathToDafnyLib_: _dafny.Seq
                def lambda41_(source69_):
                    if source69_.is_Success:
                        d_807___mcc_h6_ = source69_.v
                        def iife45_(_pat_let22_0):
                            def iife46_(d_808_p_):
                                return (d_808_p_)[0]
                            return iife46_(_pat_let22_0)
                        return iife45_(d_807___mcc_h6_)
                    elif True:
                        d_809___mcc_h7_ = source69_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_806_pathToDafnyLib_ = lambda41_((d_795_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_798_optArgs_))
                d_810_y_: _dafny.Seq
                d_810_y_ = Splitter.default__.SplitUpToTerminal(d_799_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_811_z_: _dafny.Seq
                d_811_z_ = ProofObjectBuilder.default__.BuildProofObject(d_810_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_811_z_, d_806_pathToDafnyLib_)
            elif True:
                d_812___mcc_h5_ = source68_.msg
                pass
            source70_ = (d_795_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_798_optArgs_)
            if source70_.is_Success:
                d_813___mcc_h8_ = source70_.v
                PrettyPrinters.default__.PrintInstructions(d_799_x_)
                d_814_pathToDafnyLib_: _dafny.Seq
                def lambda42_(source71_):
                    if source71_.is_Success:
                        d_815___mcc_h10_ = source71_.v
                        def iife47_(_pat_let23_0):
                            def iife48_(d_816_p_):
                                return (d_816_p_)[0]
                            return iife48_(_pat_let23_0)
                        return iife47_(d_815___mcc_h10_)
                    elif True:
                        d_817___mcc_h11_ = source71_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_814_pathToDafnyLib_ = lambda42_((d_795_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_798_optArgs_))
                d_818_y_: _dafny.Seq
                d_818_y_ = Splitter.default__.SplitUpToTerminal(d_799_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_819_z_: _dafny.Seq
                d_819_z_ = ProofObjectBuilder.default__.BuildProofObject(d_818_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_819_z_, d_814_pathToDafnyLib_)
            elif True:
                d_820___mcc_h9_ = source70_.msg
                pass
            source72_ = (d_795_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_798_optArgs_)
            if source72_.is_Success:
                d_821___mcc_h12_ = source72_.v
                d_822_m_ = d_821___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_823_y_: _dafny.Seq
                d_823_y_ = Splitter.default__.SplitUpToTerminal(d_799_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_823_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_822_m_)[0])) == (0)) or (not(default__.IsNatNumber((d_822_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_824_maxDepth_: int
                    d_824_maxDepth_ = default__.StringToNat((d_822_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_824_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_825_startAddress_: int
                    d_825_startAddress_ = ((d_823_y_)[0]).StartAddress()
                    pat_let_tv47_ = d_825_startAddress_
                    d_826_startState_: State.AState
                    def iife49_(_pat_let24_0):
                        def iife50_(d_827_dt__update__tmp_h0_):
                            def iife51_(_pat_let25_0):
                                def iife52_(d_828_dt__update_hpc_h0_):
                                    return State.AState_EState(d_828_dt__update_hpc_h0_, (d_827_dt__update__tmp_h0_).stack)
                                return iife52_(_pat_let25_0)
                            return iife51_(pat_let_tv47_)
                        return iife50_(_pat_let24_0)
                    d_826_startState_ = iife49_(State.default__.DEFAULT__VALIDSTATE)
                    if (((d_823_y_)[0]).StartAddress()) != (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment 0 does not start at address 0.\n"))).VerbatimString(False))
                    elif True:
                        d_829_g_: CFGraph.BoolCFGraph
                        d_829_g_ = BuildCFGraph.default__.BuildCFGV4(d_823_y_, d_824_maxDepth_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]))
                        if ((d_795_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_798_optArgs_)).is_Success:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_829_g_).DOTPrint(d_823_y_)).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Computing Minimised CFG\n"))).VerbatimString(False))
                        d_830_g_k_: CFGraph.BoolCFGraph
                        d_830_g_k_ = (d_829_g_).Minimise()
                        if not((d_830_g_k_).IsValid()):
                            raise _dafny.HaltException("src/dafny/Driver.dfy(138,14): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                        _dafny.print(((d_830_g_k_).DOTPrint(d_823_y_)).VerbatimString(False))
            elif True:
                d_831___mcc_h13_ = source72_.msg
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
                    source73_ = default__.CharToDigit((s)[0])
                    if source73_.is_None:
                        return False
                    elif True:
                        d_832___mcc_h0_ = source73_.v
                        d_833_v_ = d_832___mcc_h0_
                        in132_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        s = in132_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_834_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_834_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

