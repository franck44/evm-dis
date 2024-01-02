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

# Module: SeqOfSets

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SetU(xs):
        d_820___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.Set({})) | (d_820___accumulator_)
                elif True:
                    d_820___accumulator_ = (d_820___accumulator_) | ((xs)[0])
                    in88_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in88_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetI(xs):
        if (len(xs)) == (0):
            return _dafny.Set({})
        elif (len(xs)) == (1):
            return (xs)[0]
        elif True:
            return ((xs)[0]).intersection(default__.SetI(_dafny.SeqWithoutIsStrInference((xs)[1::])))

    @staticmethod
    def SplitSet(xs, f):
        d_821_asSeq_ = default__.SetToSequence(xs)
        return default__.SplitSeqTail(d_821_asSeq_, f, _dafny.Set({}), _dafny.Set({}), 0)

    @staticmethod
    def SplitSeqOfSet(xs, f):
        d_822___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_822___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_822___accumulator_ = (d_822___accumulator_) + (_dafny.SeqWithoutIsStrInference([default__.SplitSet((xs)[0], f)]))
                    in89_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in90_ = f
                    xs = in89_
                    f = in90_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetToSequence(s):
        d_823___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv5_ = s
                if (s) == (_dafny.Set({})):
                    return (d_823___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife12_(_let_dummy_6):
                        d_824_x_: int = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: int
                            for assign_such_that_0_ in (s).Elements:
                                d_824_x_ = assign_such_that_0_
                                def lambda41_(forall_var_9_):
                                    d_825_y_: int = forall_var_9_
                                    return not ((d_825_y_) in (s)) or ((d_824_x_) <= (d_825_y_))

                                if ((d_824_x_) in (s)) and (_dafny.quantifier((s).Elements, True, lambda41_)):
                                    raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value (line 218)")
                            pass
                        return (_dafny.SeqWithoutIsStrInference([d_824_x_])) + (default__.SetToSequence((pat_let_tv5_) - (_dafny.Set({d_824_x_}))))
                    return iife12_(0)
                    
                break

    @staticmethod
    def SplitSeqTail(xs, f, cTrue, cFalse, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return (cTrue, cFalse)
                elif f((xs)[index]):
                    in91_ = xs
                    in92_ = f
                    in93_ = (cTrue) | (_dafny.Set({(xs)[index]}))
                    in94_ = cFalse
                    in95_ = (index) + (1)
                    xs = in91_
                    f = in92_
                    cTrue = in93_
                    cFalse = in94_
                    index = in95_
                    raise _dafny.TailCall()
                elif True:
                    in96_ = xs
                    in97_ = f
                    in98_ = cTrue
                    in99_ = (cFalse) | (_dafny.Set({(xs)[index]}))
                    in100_ = (index) + (1)
                    xs = in96_
                    f = in97_
                    cTrue = in98_
                    cFalse = in99_
                    index = in100_
                    raise _dafny.TailCall()
                break

