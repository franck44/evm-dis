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
import EVMObject
import ArgParser

# Module: SeqOfSets

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SetU(xs):
        d_828___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.Set({})) | (d_828___accumulator_)
                elif True:
                    d_828___accumulator_ = (d_828___accumulator_) | ((xs)[0])
                    in92_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in92_
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
    def AllNonEmpty(xs):
        def lambda39_(forall_var_10_):
            d_829_k_: int = forall_var_10_
            return not (((0) <= (d_829_k_)) and ((d_829_k_) < (len(xs)))) or (((xs)[d_829_k_]) != (_dafny.Set({})))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(xs)), True, lambda39_)

    @staticmethod
    def DisjointAnyTwo(xs):
        def lambda40_(forall_var_11_):
            def lambda41_(forall_var_12_):
                d_831_k_k_: int = forall_var_12_
                return not ((((0) <= (d_830_k_)) and ((d_830_k_) < (d_831_k_k_))) and ((d_831_k_k_) < (len(xs)))) or ((((xs)[d_830_k_]).intersection((xs)[d_831_k_k_])) == (_dafny.Set({})))

            d_830_k_: int = forall_var_11_
            return _dafny.quantifier(_dafny.IntegerRange((d_830_k_) + (1), len(xs)), True, lambda41_)

        return _dafny.quantifier(_dafny.IntegerRange(0, len(xs)), True, lambda40_)

    @staticmethod
    def SetN(xs, n):
        def iife0_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, n):
                d_832_z_: int = compr_0_
                if ((0) <= (d_832_z_)) and ((d_832_z_) < (n)):
                    coll0_ = coll0_.union(_dafny.Set([d_832_z_]))
            return _dafny.Set(coll0_)
        return (default__.SetU(xs)) == (iife0_()
        )

    @staticmethod
    def SplitSet(xs, f):
        d_833_asSeq_ = default__.SetToSequence(xs)
        return default__.SplitSeqTail(d_833_asSeq_, f, _dafny.Set({}), _dafny.Set({}), 0)

    @staticmethod
    def SplitSeqOfSet(xs, f):
        d_834___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_834___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_834___accumulator_ = (d_834___accumulator_) + (_dafny.SeqWithoutIsStrInference([default__.SplitSet((xs)[0], f)]))
                    in93_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in94_ = f
                    xs = in93_
                    f = in94_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetToSequence(s):
        d_835___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv0_ = s
                if (s) == (_dafny.Set({})):
                    return (d_835___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife1_(_let_dummy_0):
                        d_836_x_: int = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: int
                            for assign_such_that_0_ in (s).Elements:
                                d_836_x_ = assign_such_that_0_
                                def lambda42_(forall_var_13_):
                                    d_837_y_: int = forall_var_13_
                                    return not ((d_837_y_) in (s)) or ((d_836_x_) <= (d_837_y_))

                                if ((d_836_x_) in (s)) and (_dafny.quantifier((s).Elements, True, lambda42_)):
                                    raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value (line 193)")
                            pass
                        return (_dafny.SeqWithoutIsStrInference([d_836_x_])) + (default__.SetToSequence((pat_let_tv0_) - (_dafny.Set({d_836_x_}))))
                    return iife1_(0)
                    
                break

    @staticmethod
    def SplitSeqTail(xs, f, cTrue, cFalse, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return (cTrue, cFalse)
                elif f((xs)[index]):
                    in95_ = xs
                    in96_ = f
                    in97_ = (cTrue) | (_dafny.Set({(xs)[index]}))
                    in98_ = cFalse
                    in99_ = (index) + (1)
                    xs = in95_
                    f = in96_
                    cTrue = in97_
                    cFalse = in98_
                    index = in99_
                    raise _dafny.TailCall()
                elif True:
                    in100_ = xs
                    in101_ = f
                    in102_ = cTrue
                    in103_ = (cFalse) | (_dafny.Set({(xs)[index]}))
                    in104_ = (index) + (1)
                    xs = in100_
                    f = in101_
                    cTrue = in102_
                    cFalse = in103_
                    index = in104_
                    raise _dafny.TailCall()
                break

