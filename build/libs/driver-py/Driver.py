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

# Module: Driver

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        if (len(args)) < (2):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not enough arguments\n"))).VerbatimString(False))
            _dafny.print((default__.usageMsg).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        elif (len(args)) == (2):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassembling code"))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            d_202_x_: _dafny.Seq
            d_202_x_ = BinaryDecoder.default__.Disassemble((args)[1], _dafny.SeqWithoutIsStrInference([]), 0)
            PrettyPrinters.default__.PrintInstructions(d_202_x_)
        elif True:
            if ((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-d"))):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Disassembling code"))).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                d_203_x_: _dafny.Seq
                d_203_x_ = BinaryDecoder.default__.Disassemble((args)[2], _dafny.SeqWithoutIsStrInference([]), 0)
                PrettyPrinters.default__.PrintInstructions(d_203_x_)
            elif ((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-p"))):
                d_204_x_: _dafny.Seq
                d_204_x_ = BinaryDecoder.default__.Disassemble((args)[2], _dafny.SeqWithoutIsStrInference([]), 0)
                d_205_y_: _dafny.Seq
                d_205_y_ = Splitter.default__.SplitUpToTerminal(d_204_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_206_z_: _dafny.Seq
                d_206_z_ = ProofObjectBuilder.default__.BuildProofObject(d_205_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_206_z_, 0)
            elif ((args)[1]) == (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "-a"))):
                d_207_x_: _dafny.Seq
                d_207_x_ = BinaryDecoder.default__.Disassemble((args)[2], _dafny.SeqWithoutIsStrInference([]), 0)
                PrettyPrinters.default__.PrintInstructions(d_207_x_)
                d_208_y_: _dafny.Seq
                d_208_y_ = Splitter.default__.SplitUpToTerminal(d_207_x_, _dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
                d_209_z_: _dafny.Seq
                d_209_z_ = ProofObjectBuilder.default__.BuildProofObject(d_208_y_)
                PrettyPrinters.default__.PrintProofObjectToDafny(d_209_z_, 0)
            elif True:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot parse arguments "))).VerbatimString(False))
                _dafny.print(((args)[1]).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                _dafny.print((default__.usageMsg).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @_dafny.classproperty
    def usageMsg(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Usage: \n -d <string> or <string>: disassemble <string>\n -p <string>: Proof object\n -a: both -d and -p"))
