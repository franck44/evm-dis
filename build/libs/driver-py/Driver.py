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
        d_948_optionParser_: ArgParser.ArgumentParser
        nw1_ = ArgParser.ArgumentParser()
        nw1_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<string>")))
        d_948_optionParser_ = nw1_
        (d_948_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassemble <string>")))
        (d_948_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Generate proof object for <string>")))
        (d_948_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-s")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Print segment of <string>")))
        (d_948_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Same as -d -p")))
        (d_948_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-l")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The path to the Dafny-EVM source code. Used to add includes files in the proof object. ")))
        (d_948_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-c")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Max depth. Control flow graph in DOT format")))
        (d_948_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-r")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), 1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display non-minimised and minimised CFGs")))
        (d_948_optionParser_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-f")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Use exit and entry ports in segments do draw arrows (apply minimised only).")))
        if ((len(args)) < (2)) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            (d_948_optionParser_).PrintHelp()
        elif (len(args)) == (2):
            d_949_x_: _dafny.Seq
            d_949_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_949_x_)
        elif (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")))) or (((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")))):
            (d_948_optionParser_).PrintHelp()
        elif True:
            d_950_stringToProcess_: _dafny.Seq
            d_950_stringToProcess_ = (args)[(len(args)) - (1)]
            d_951_optArgs_: _dafny.Seq
            d_951_optArgs_ = _dafny.SeqWithoutIsStrInference((args)[1:(len(args)) - (1):])
            d_952_x_: _dafny.Seq
            d_952_x_ = BinaryDecoder.default__.Disassemble(d_950_stringToProcess_, _dafny.SeqWithoutIsStrInference([]), 0)
            source68_ = (d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--dis")), d_951_optArgs_)
            if source68_.is_Success:
                d_953___mcc_h0_ = source68_.v
                PrettyPrinters.default__.PrintInstructions(d_952_x_)
            elif True:
                d_954___mcc_h1_ = source68_.msg
                pass
            source69_ = (d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--segment")), d_951_optArgs_)
            if source69_.is_Success:
                d_955___mcc_h2_ = source69_.v
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segments:\n"))).VerbatimString(False))
                d_956_y_: _dafny.Seq
                d_956_y_ = Splitter.default__.SplitUpToTerminal(d_952_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                PrettyPrinters.default__.PrintSegments(d_956_y_, 0)
            elif True:
                d_957___mcc_h3_ = source69_.msg
                pass
            source70_ = (d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--proof")), d_951_optArgs_)
            if source70_.is_Success:
                d_958___mcc_h4_ = source70_.v
                d_959_pathToDafnyLib_: _dafny.Seq
                def lambda56_(source71_):
                    if source71_.is_Success:
                        d_960___mcc_h6_ = source71_.v
                        def iife45_(_pat_let22_0):
                            def iife46_(d_961_p_):
                                return (d_961_p_)[0]
                            return iife46_(_pat_let22_0)
                        return iife45_(d_960___mcc_h6_)
                    elif True:
                        d_962___mcc_h7_ = source71_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_959_pathToDafnyLib_ = lambda56_((d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_951_optArgs_))
                d_963_y_: _dafny.Seq
                d_963_y_ = Splitter.default__.SplitUpToTerminal(d_952_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_964_z_: _dafny.Seq
                d_964_z_ = ProofObjectBuilder.default__.BuildProofObject(d_963_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_964_z_, d_959_pathToDafnyLib_)
            elif True:
                d_965___mcc_h5_ = source70_.msg
                pass
            source72_ = (d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--all")), d_951_optArgs_)
            if source72_.is_Success:
                d_966___mcc_h8_ = source72_.v
                PrettyPrinters.default__.PrintInstructions(d_952_x_)
                d_967_pathToDafnyLib_: _dafny.Seq
                def lambda57_(source73_):
                    if source73_.is_Success:
                        d_968___mcc_h10_ = source73_.v
                        def iife47_(_pat_let23_0):
                            def iife48_(d_969_p_):
                                return (d_969_p_)[0]
                            return iife48_(_pat_let23_0)
                        return iife47_(d_968___mcc_h10_)
                    elif True:
                        d_970___mcc_h11_ = source73_.msg
                        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                d_967_pathToDafnyLib_ = lambda57_((d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--lib")), d_951_optArgs_))
                d_971_y_: _dafny.Seq
                d_971_y_ = Splitter.default__.SplitUpToTerminal(d_952_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_972_z_: _dafny.Seq
                d_972_z_ = ProofObjectBuilder.default__.BuildProofObject(d_971_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_972_z_, d_967_pathToDafnyLib_)
            elif True:
                d_973___mcc_h9_ = source72_.msg
                pass
            source74_ = (d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--cfg")), d_951_optArgs_)
            if source74_.is_Success:
                d_974___mcc_h12_ = source74_.v
                d_975_m_ = d_974___mcc_h12_
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "CFG:\n"))).VerbatimString(False))
                d_976_y_: _dafny.Seq
                d_976_y_ = Splitter.default__.SplitUpToTerminal(d_952_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                if (len(d_976_y_)) == (0):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found\n"))).VerbatimString(False))
                elif ((len((d_975_m_)[0])) == (0)) or (not(default__.IsNatNumber((d_975_m_)[0]))):
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Argument to --cfg is not a nat.\n"))).VerbatimString(False))
                elif True:
                    d_977_maxDepth_: int
                    d_977_maxDepth_ = default__.StringToNat((d_975_m_)[0], 0)
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "maxDepth is:"))).VerbatimString(False))
                    _dafny.print(_dafny.string_of(d_977_maxDepth_))
                    _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                    d_978_startAddress_: int
                    d_978_startAddress_ = ((d_976_y_)[0]).StartAddress()
                    pat_let_tv47_ = d_978_startAddress_
                    d_979_startState_: State.AState
                    def iife49_(_pat_let24_0):
                        def iife50_(d_980_dt__update__tmp_h0_):
                            def iife51_(_pat_let25_0):
                                def iife52_(d_981_dt__update_hpc_h0_):
                                    return State.AState_EState(d_981_dt__update_hpc_h0_, (d_980_dt__update__tmp_h0_).stack)
                                return iife52_(_pat_let25_0)
                            return iife51_(pat_let_tv47_)
                        return iife50_(_pat_let24_0)
                    d_979_startState_ = iife49_(State.default__.DEFAULT__VALIDSTATE)
                    if (((d_976_y_)[0]).StartAddress()) != (0):
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment 0 does not start at address 0.\n"))).VerbatimString(False))
                    elif True:
                        d_982_g_: CFGraph.BoolCFGraph
                        d_982_g_ = BuildCFGraph.default__.BuildCFGV4(d_976_y_, d_977_maxDepth_, 0, State.default__.DEFAULT__VALIDSTATE, _dafny.SeqWithoutIsStrInference([CFGraph.CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))]), _dafny.SeqWithoutIsStrInference([0]), _dafny.SeqWithoutIsStrInference([]))
                        if ((d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--raw")), d_951_optArgs_)).is_Success:
                            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Raw CFG\n"))).VerbatimString(False))
                            _dafny.print(((d_982_g_).DOTPrint(d_976_y_, False)).VerbatimString(False))
                        d_983_fancy_: bool
                        d_983_fancy_ = ((d_948_optionParser_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--fancy")), d_951_optArgs_)).is_Success
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Computing Minimised CFG\n"))).VerbatimString(False))
                        d_984_g_k_: CFGraph.BoolCFGraph
                        d_984_g_k_ = (d_982_g_).Minimise()
                        if not((d_984_g_k_).IsValid()):
                            raise _dafny.HaltException("src/dafny/Driver.dfy(140,14): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
                        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimised CFG\n"))).VerbatimString(False))
                        _dafny.print(((d_984_g_k_).DOTPrint(d_976_y_, d_983_fancy_)).VerbatimString(False))
            elif True:
                d_985___mcc_h13_ = source74_.msg
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
                    source75_ = default__.CharToDigit((s)[0])
                    if source75_.is_None:
                        return False
                    elif True:
                        d_986___mcc_h0_ = source75_.v
                        d_987_v_ = d_986___mcc_h0_
                        in145_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                        s = in145_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def StringToNat(s, lastVal):
        if (len(s)) == (1):
            return (default__.CharToDigit((s)[0])).v
        elif True:
            d_988_v_ = (default__.CharToDigit((s)[(len(s)) - (1)])).v
            return (d_988_v_) + ((10) * (default__.StringToNat(_dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):]), 0)))

