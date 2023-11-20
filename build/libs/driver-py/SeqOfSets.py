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

# Module: SeqOfSets

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SetU(xs):
        d_648___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.Set({})) | (d_648___accumulator_)
                elif True:
                    d_648___accumulator_ = (d_648___accumulator_) | ((xs)[0])
                    in82_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in82_
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
        def lambda18_(forall_var_4_):
            d_649_k_: int = forall_var_4_
            return not (((0) <= (d_649_k_)) and ((d_649_k_) < (len(xs)))) or (((xs)[d_649_k_]) != (_dafny.Set({})))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(xs)), True, lambda18_)

    @staticmethod
    def DisjointAnyTwo(xs):
        def lambda19_(forall_var_5_):
            def lambda20_(forall_var_6_):
                d_651_k_k_: int = forall_var_6_
                return not ((((0) <= (d_650_k_)) and ((d_650_k_) < (d_651_k_k_))) and ((d_651_k_k_) < (len(xs)))) or ((((xs)[d_650_k_]).intersection((xs)[d_651_k_k_])) == (_dafny.Set({})))

            d_650_k_: int = forall_var_5_
            return _dafny.quantifier(_dafny.IntegerRange((d_650_k_) + (1), len(xs)), True, lambda20_)

        return _dafny.quantifier(_dafny.IntegerRange(0, len(xs)), True, lambda19_)

    @staticmethod
    def SetN(xs, n):
        def iife2_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, n):
                d_652_z_: int = compr_0_
                if ((0) <= (d_652_z_)) and ((d_652_z_) < (n)):
                    coll0_ = coll0_.union(_dafny.Set([d_652_z_]))
            return _dafny.Set(coll0_)
        return (default__.SetU(xs)) == (iife2_()
        )

    @staticmethod
    def SplitSet(xs, f):
        d_653_asSeq_ = default__.SetToSequence(xs)
        return default__.SplitSeqTail(d_653_asSeq_, f, _dafny.Set({}), _dafny.Set({}), 0)

    @staticmethod
    def SplitSeqOfSet(xs, f):
        d_654___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_654___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_654___accumulator_ = (d_654___accumulator_) + (_dafny.SeqWithoutIsStrInference([default__.SplitSet((xs)[0], f)]))
                    in83_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in84_ = f
                    xs = in83_
                    f = in84_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetToSequence(s):
        d_655___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv1_ = s
                if (s) == (_dafny.Set({})):
                    return (d_655___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife3_(_let_dummy_1):
                        d_656_x_: int = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: int
                            for assign_such_that_0_ in (s).Elements:
                                d_656_x_ = assign_such_that_0_
                                def lambda21_(forall_var_7_):
                                    d_657_y_: int = forall_var_7_
                                    return not ((d_657_y_) in (s)) or ((d_656_x_) <= (d_657_y_))

                                if ((d_656_x_) in (s)) and (_dafny.quantifier((s).Elements, True, lambda21_)):
                                    raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value (line 193)")
                            pass
                        return (_dafny.SeqWithoutIsStrInference([d_656_x_])) + (default__.SetToSequence((pat_let_tv1_) - (_dafny.Set({d_656_x_}))))
                    return iife3_(0)
                    
                break

    @staticmethod
    def SplitSeqTail(xs, f, cTrue, cFalse, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return (cTrue, cFalse)
                elif f((xs)[index]):
                    in85_ = xs
                    in86_ = f
                    in87_ = (cTrue) | (_dafny.Set({(xs)[index]}))
                    in88_ = cFalse
                    in89_ = (index) + (1)
                    xs = in85_
                    f = in86_
                    cTrue = in87_
                    cFalse = in88_
                    index = in89_
                    raise _dafny.TailCall()
                elif True:
                    in90_ = xs
                    in91_ = f
                    in92_ = cTrue
                    in93_ = (cFalse) | (_dafny.Set({(xs)[index]}))
                    in94_ = (index) + (1)
                    xs = in90_
                    f = in91_
                    cTrue = in92_
                    cFalse = in93_
                    index = in94_
                    raise _dafny.TailCall()
                break

