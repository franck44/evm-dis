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
import ProofObjectBuilder

# Module: ArgParser

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def default_Main_():
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "hello! Testing ArgParser!\n"))).VerbatimString(False))
        d_788_cli_: ArgumentParser
        nw0_ = ArgumentParser()
        nw0_.ctor__(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<filename>")))
        d_788_cli_ = nw0_
        (d_788_cli_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-o")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--one")), 0, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No help provided")))
        (d_788_cli_).AddOption(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-tw")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--two")), 2, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "don't do that!")))
        d_789_r_: _dafny.Seq
        d_789_r_ = _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-one")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--two")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a1")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a2")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-unknwon"))])
        source55_ = (d_788_cli_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-o")), d_789_r_)
        if source55_.is_Success:
            d_790___mcc_h0_ = source55_.v
            d_791_a_ = d_790___mcc_h0_
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Success -o! has arguments:"))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_791_a_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        elif True:
            d_792___mcc_h1_ = source55_.msg
            d_793_m_ = d_792___mcc_h1_
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No -o! "))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        source56_ = (d_788_cli_).GetArgs(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "--two")), d_789_r_)
        if source56_.is_Success:
            d_794___mcc_h2_ = source56_.v
            d_795_a_ = d_794___mcc_h2_
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Success -two! has arguments: "))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_795_a_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        elif True:
            d_796___mcc_h3_ = source56_.msg
            d_797_m_ = d_796___mcc_h3_
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No --two! "))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        (d_788_cli_).PrintHelp()


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
        hi0_ = len(self.knownKeys)
        for d_798_i_ in range(0, hi0_):
            d_799_k_: CLIOption
            d_799_k_ = (self.knownArgs)[(self.knownKeys)[d_798_i_]]
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ["))).VerbatimString(False))
            _dafny.print(((self.knownKeys)[d_798_i_]).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "] "))).VerbatimString(False))
            hi1_ = (d_799_k_).numArgs
            for d_800_i_ in range(0, hi1_):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " arg"))).VerbatimString(False))
                _dafny.print(_dafny.string_of(d_800_i_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " "))).VerbatimString(False))
        _dafny.print((self.usageSuffix).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "options"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        d_801_maxL_: int
        d_801_maxL_ = (self).MaxValueFast(self.knownKeys, 0)
        hi2_ = len(self.knownKeys)
        for d_802_i_ in range(0, hi2_):
            d_803_k_: CLIOption
            d_803_k_ = (self.knownArgs)[(self.knownKeys)[d_802_i_]]
            _dafny.print(((self.knownKeys)[d_802_i_]).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint(' ') for d_804___v0_ in range(((d_801_maxL_) - (len((self.knownKeys)[d_802_i_]))) + (2))])).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ["))).VerbatimString(False))
            _dafny.print(((d_803_k_).name).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "] "))).VerbatimString(False))
            _dafny.print(((d_803_k_).desc).VerbatimString(False))
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
                    d_805_opt_ = (_this.knownArgs)[key]
                    d_806_numArgs_ = (d_805_opt_).numArgs
                    if (len(_dafny.SeqWithoutIsStrInference((s)[1::]))) < (d_806_numArgs_):
                        return MiscTypes.Try_Failure(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "argument "))) + ((s)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " needs more arguments"))))
                    elif True:
                        return MiscTypes.Try_Success(_dafny.SeqWithoutIsStrInference((_dafny.SeqWithoutIsStrInference((s)[1::]))[:d_806_numArgs_:]))
                elif True:
                    in83_ = _this
                    in84_ = key
                    in85_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    _this = in83_
                    
                    key = in84_
                    s = in85_
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
                    in86_ = _this
                    in87_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    in88_ = Int.default__.Max(len((s)[0]), max)
                    _this = in86_
                    
                    s = in87_
                    max = in88_
                    raise _dafny.TailCall()
                break

