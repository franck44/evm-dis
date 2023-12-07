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
import ArgParser

# Module: SeqOfSets

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SetU(xs):
        d_807___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.Set({})) | (d_807___accumulator_)
                elif True:
                    d_807___accumulator_ = (d_807___accumulator_) | ((xs)[0])
                    in89_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in89_
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
        def lambda33_(forall_var_4_):
            d_808_k_: int = forall_var_4_
            return not (((0) <= (d_808_k_)) and ((d_808_k_) < (len(xs)))) or (((xs)[d_808_k_]) != (_dafny.Set({})))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(xs)), True, lambda33_)

    @staticmethod
    def DisjointAnyTwo(xs):
        def lambda34_(forall_var_5_):
            def lambda35_(forall_var_6_):
                d_810_k_k_: int = forall_var_6_
                return not ((((0) <= (d_809_k_)) and ((d_809_k_) < (d_810_k_k_))) and ((d_810_k_k_) < (len(xs)))) or ((((xs)[d_809_k_]).intersection((xs)[d_810_k_k_])) == (_dafny.Set({})))

            d_809_k_: int = forall_var_5_
            return _dafny.quantifier(_dafny.IntegerRange((d_809_k_) + (1), len(xs)), True, lambda35_)

        return _dafny.quantifier(_dafny.IntegerRange(0, len(xs)), True, lambda34_)

    @staticmethod
    def SetN(xs, n):
        def iife2_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, n):
                d_811_z_: int = compr_0_
                if ((0) <= (d_811_z_)) and ((d_811_z_) < (n)):
                    coll0_ = coll0_.union(_dafny.Set([d_811_z_]))
            return _dafny.Set(coll0_)
        return (default__.SetU(xs)) == (iife2_()
        )

    @staticmethod
    def SplitSet(xs, f):
        d_812_asSeq_ = default__.SetToSequence(xs)
        return default__.SplitSeqTail(d_812_asSeq_, f, _dafny.Set({}), _dafny.Set({}), 0)

    @staticmethod
    def SplitSeqOfSet(xs, f):
        d_813___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_813___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_813___accumulator_ = (d_813___accumulator_) + (_dafny.SeqWithoutIsStrInference([default__.SplitSet((xs)[0], f)]))
                    in90_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in91_ = f
                    xs = in90_
                    f = in91_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetToSequence(s):
        d_814___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv1_ = s
                if (s) == (_dafny.Set({})):
                    return (d_814___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife3_(_let_dummy_1):
                        d_815_x_: int = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: int
                            for assign_such_that_0_ in (s).Elements:
                                d_815_x_ = assign_such_that_0_
                                def lambda36_(forall_var_7_):
                                    d_816_y_: int = forall_var_7_
                                    return not ((d_816_y_) in (s)) or ((d_815_x_) <= (d_816_y_))

                                if ((d_815_x_) in (s)) and (_dafny.quantifier((s).Elements, True, lambda36_)):
                                    raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value (line 193)")
                            pass
                        return (_dafny.SeqWithoutIsStrInference([d_815_x_])) + (default__.SetToSequence((pat_let_tv1_) - (_dafny.Set({d_815_x_}))))
                    return iife3_(0)
                    
                break

    @staticmethod
    def SplitSeqTail(xs, f, cTrue, cFalse, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return (cTrue, cFalse)
                elif f((xs)[index]):
                    in92_ = xs
                    in93_ = f
                    in94_ = (cTrue) | (_dafny.Set({(xs)[index]}))
                    in95_ = cFalse
                    in96_ = (index) + (1)
                    xs = in92_
                    f = in93_
                    cTrue = in94_
                    cFalse = in95_
                    index = in96_
                    raise _dafny.TailCall()
                elif True:
                    in97_ = xs
                    in98_ = f
                    in99_ = cTrue
                    in100_ = (cFalse) | (_dafny.Set({(xs)[index]}))
                    in101_ = (index) + (1)
                    xs = in97_
                    f = in98_
                    cTrue = in99_
                    cFalse = in100_
                    index = in101_
                    raise _dafny.TailCall()
                break

