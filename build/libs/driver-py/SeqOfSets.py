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
        d_604___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.Set({})) | (d_604___accumulator_)
                elif True:
                    d_604___accumulator_ = (d_604___accumulator_) | ((xs)[0])
                    in70_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in70_
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
            d_605_k_: int = forall_var_4_
            return not (((0) <= (d_605_k_)) and ((d_605_k_) < (len(xs)))) or (((xs)[d_605_k_]) != (_dafny.Set({})))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(xs)), True, lambda18_)

    @staticmethod
    def DisjointAnyTwo(xs):
        def lambda19_(forall_var_5_):
            def lambda20_(forall_var_6_):
                d_607_k_k_: int = forall_var_6_
                return not ((((0) <= (d_606_k_)) and ((d_606_k_) < (d_607_k_k_))) and ((d_607_k_k_) < (len(xs)))) or ((((xs)[d_606_k_]).intersection((xs)[d_607_k_k_])) == (_dafny.Set({})))

            d_606_k_: int = forall_var_5_
            return _dafny.quantifier(_dafny.IntegerRange((d_606_k_) + (1), len(xs)), True, lambda20_)

        return _dafny.quantifier(_dafny.IntegerRange(0, len(xs)), True, lambda19_)

    @staticmethod
    def SetN(xs, n):
        def iife2_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, n):
                d_608_z_: int = compr_0_
                if ((0) <= (d_608_z_)) and ((d_608_z_) < (n)):
                    coll0_ = coll0_.union(_dafny.Set([d_608_z_]))
            return _dafny.Set(coll0_)
        return (default__.SetU(xs)) == (iife2_()
        )

    @staticmethod
    def SplitSet(xs, f):
        d_609_asSeq_ = default__.SetToSequence(xs)
        return default__.SplitSeqTail(d_609_asSeq_, f, _dafny.Set({}), _dafny.Set({}), 0)

    @staticmethod
    def SplitSeqOfSet(xs, f):
        d_610___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_610___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_610___accumulator_ = (d_610___accumulator_) + (_dafny.SeqWithoutIsStrInference([default__.SplitSet((xs)[0], f)]))
                    in71_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in72_ = f
                    xs = in71_
                    f = in72_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetToSequence(s):
        d_611___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv1_ = s
                if (s) == (_dafny.Set({})):
                    return (d_611___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife3_(_let_dummy_1):
                        d_612_x_: int = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: int
                            for assign_such_that_0_ in (s).Elements:
                                d_612_x_ = assign_such_that_0_
                                def lambda21_(forall_var_7_):
                                    d_613_y_: int = forall_var_7_
                                    return not ((d_613_y_) in (s)) or ((d_612_x_) <= (d_613_y_))

                                if ((d_612_x_) in (s)) and (_dafny.quantifier((s).Elements, True, lambda21_)):
                                    raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value (line 193)")
                            pass
                        return (_dafny.SeqWithoutIsStrInference([d_612_x_])) + (default__.SetToSequence((pat_let_tv1_) - (_dafny.Set({d_612_x_}))))
                    return iife3_(0)
                    
                break

    @staticmethod
    def SplitSeqTail(xs, f, cTrue, cFalse, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return (cTrue, cFalse)
                elif f((xs)[index]):
                    in73_ = xs
                    in74_ = f
                    in75_ = (cTrue) | (_dafny.Set({(xs)[index]}))
                    in76_ = cFalse
                    in77_ = (index) + (1)
                    xs = in73_
                    f = in74_
                    cTrue = in75_
                    cFalse = in76_
                    index = in77_
                    raise _dafny.TailCall()
                elif True:
                    in78_ = xs
                    in79_ = f
                    in80_ = cTrue
                    in81_ = (cFalse) | (_dafny.Set({(xs)[index]}))
                    in82_ = (index) + (1)
                    xs = in78_
                    f = in79_
                    cTrue = in80_
                    cFalse = in81_
                    index = in82_
                    raise _dafny.TailCall()
                break

