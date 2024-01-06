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

# Module: ArgParser

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def default_Main_():
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "hello! Testing ArgParser!\n"))).VerbatimString(False))
        d_1011_cli_: ArgumentParser
        nw0_ = ArgumentParser()
        nw0_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<filename>")))
        d_1011_cli_ = nw0_
        (d_1011_cli_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-o")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--one")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No help provided")))
        (d_1011_cli_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-tw")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--two")), 2, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "don't do that!")))
        d_1012_r_: _dafny.Seq
        d_1012_r_ = _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-one")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--two")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a1")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a2")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-unknwon"))])
        source68_ = (d_1011_cli_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-o")), d_1012_r_)
        if source68_.is_Success:
            d_1013___mcc_h0_ = source68_.v
            d_1014_a_ = d_1013___mcc_h0_
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Success -o! has arguments:"))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_1014_a_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        elif True:
            d_1015___mcc_h1_ = source68_.msg
            d_1016_m_ = d_1015___mcc_h1_
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No -o! "))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        source69_ = (d_1011_cli_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--two")), d_1012_r_)
        if source69_.is_Success:
            d_1017___mcc_h2_ = source69_.v
            d_1018_a_ = d_1017___mcc_h2_
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Success -two! has arguments: "))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_1018_a_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        elif True:
            d_1019___mcc_h3_ = source69_.msg
            d_1020_m_ = d_1019___mcc_h3_
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No --two! "))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        (d_1011_cli_).PrintHelp()


class CLIOption:
    @classmethod
    def default(cls, ):
        return lambda: CLIOption_CLIOption(_dafny.Seq({}), int(0), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CLIOption(self) -> bool:
        return isinstance(self, CLIOption_CLIOption)

class CLIOption_CLIOption(CLIOption, NamedTuple('CLIOption', [('name', Any), ('numArgs', Any), ('desc', Any)])):
    def __dafnystr__(self) -> str:
        return f'ArgParser.CLIOption.CLIOption({self.name.VerbatimString(True)}, {_dafny.string_of(self.numArgs)}, {self.desc.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CLIOption_CLIOption) and self.name == __o.name and self.numArgs == __o.numArgs and self.desc == __o.desc
    def __hash__(self) -> int:
        return super().__hash__()


class ArgumentParser:
    def  __init__(self):
        self.knownArgs: _dafny.Map = _dafny.Map({})
        self.knownNameArgs: _dafny.Map = _dafny.Map({})
        self.knownKeys: _dafny.Seq = _dafny.Seq({})
        self.usageSuffix: _dafny.Seq = _dafny.Seq({})
        pass

    def __dafnystr__(self) -> str:
        return "ArgParser.ArgumentParser"
    def ctor__(self, s):
        (self).usageSuffix = s
        (self).knownArgs = _dafny.Map({_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help")): CLIOption_CLIOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Display help and exit")))})
        (self).knownNameArgs = _dafny.Map({_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-h")): _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help"))})
        (self).knownKeys = _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--help"))])

    def AddOption(self, opname, name, numArgs, help):
        (self).knownArgs = (self.knownArgs).set(name, CLIOption_CLIOption(opname, numArgs, help))
        (self).knownNameArgs = (self.knownNameArgs).set(opname, name)
        if (name) not in (self.knownKeys):
            (self).knownKeys = (self.knownKeys) + (_dafny.SeqWithoutIsStrInference([name]))

    def PrintHelp(self):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "usage: <this program> "))).VerbatimString(False))
        hi5_ = len(self.knownKeys)
        for d_1021_i_ in range(0, hi5_):
            d_1022_k_: CLIOption
            d_1022_k_ = (self.knownArgs)[(self.knownKeys)[d_1021_i_]]
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ["))).VerbatimString(False))
            _dafny.print(((self.knownKeys)[d_1021_i_]).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "] "))).VerbatimString(False))
            hi6_ = (d_1022_k_).numArgs
            for d_1023_i_ in range(0, hi6_):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " arg"))).VerbatimString(False))
                _dafny.print(_dafny.string_of(d_1023_i_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " "))).VerbatimString(False))
        _dafny.print((self.usageSuffix).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "options"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        d_1024_maxL_: int
        d_1024_maxL_ = (self).MaxValueFast(self.knownKeys, 0)
        hi7_ = len(self.knownKeys)
        for d_1025_i_ in range(0, hi7_):
            d_1026_k_: CLIOption
            d_1026_k_ = (self.knownArgs)[(self.knownKeys)[d_1025_i_]]
            _dafny.print(((self.knownKeys)[d_1025_i_]).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint(' ') for d_1027___v0_ in range(((d_1024_maxL_) - (len((self.knownKeys)[d_1025_i_]))) + (2))])).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ["))).VerbatimString(False))
            _dafny.print(((d_1026_k_).name).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "] "))).VerbatimString(False))
            _dafny.print(((d_1026_k_).desc).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def GetArgs(self, key, s):
        _this = self
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return MiscTypes.Try_Failure(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not found")))
                elif (key) not in ((_this.knownArgs).keys):
                    return MiscTypes.Try_Failure(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not a key")))
                elif ((_this).Canonical((s)[0])) == (key):
                    d_1028_opt_ = (_this.knownArgs)[key]
                    d_1029_numArgs_ = (d_1028_opt_).numArgs
                    if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < (d_1029_numArgs_):
                        return MiscTypes.Try_Failure(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "argument "))) + ((s)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " needs more arguments"))))
                    elif True:
                        return MiscTypes.Try_Success(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:d_1029_numArgs_:]))
                elif True:
                    in146_ = _this
                    in147_ = key
                    in148_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    _this = in146_
                    
                    key = in147_
                    s = in148_
                    raise _dafny.TailCall()
                break

    def Canonical(self, s):
        if (s) in (self.knownNameArgs):
            return (self.knownNameArgs)[s]
        elif True:
            return s

    def MaxValueFast(self, s, max):
        _this = self
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return max
                elif True:
                    in149_ = _this
                    in150_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    in151_ = Int.default__.Max(len((s)[0]), max)
                    _this = in149_
                    
                    s = in150_
                    max = in151_
                    raise _dafny.TailCall()
                break

