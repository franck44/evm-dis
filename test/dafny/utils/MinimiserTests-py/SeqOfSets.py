import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes

# Module: SeqOfSets

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SetU(xs):
        d_7___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.Set({})) | (d_7___accumulator_)
                elif True:
                    d_7___accumulator_ = (d_7___accumulator_) | ((xs)[0])
                    in9_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in9_
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
        d_8_asSeq_ = default__.SetToSequence(xs)
        return default__.SplitSeq(d_8_asSeq_, f)

    @staticmethod
    def SplitSeqOfSet(xs, f):
        d_9___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_9___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_9___accumulator_ = (d_9___accumulator_) + (_dafny.SeqWithoutIsStrInference([default__.SplitSet((xs)[0], f)]))
                    in10_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in11_ = f
                    xs = in10_
                    f = in11_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetToSequence(s):
        d_10___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv0_ = s
                if (s) == (_dafny.Set({})):
                    return (d_10___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife0_(_let_dummy_0):
                        d_11_x_: int = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: int
                            for assign_such_that_0_ in (s).Elements:
                                d_11_x_ = assign_such_that_0_
                                def lambda0_(forall_var_0_):
                                    d_12_y_: int = forall_var_0_
                                    return not ((d_12_y_) in (s)) or ((d_11_x_) <= (d_12_y_))

                                if ((d_11_x_) in (s)) and (_dafny.quantifier((s).Elements, True, lambda0_)):
                                    raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value (line 77)")
                            pass
                        return (_dafny.SeqWithoutIsStrInference([d_11_x_])) + (default__.SetToSequence((pat_let_tv0_) - (_dafny.Set({d_11_x_}))))
                    return iife0_(0)
                    
                break

    @staticmethod
    def SplitSeqTail(xs, f, cTrue, cFalse, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return (cTrue, cFalse)
                elif f((xs)[index]):
                    in12_ = xs
                    in13_ = f
                    in14_ = (cTrue) | (_dafny.Set({(xs)[index]}))
                    in15_ = cFalse
                    in16_ = (index) + (1)
                    xs = in12_
                    f = in13_
                    cTrue = in14_
                    cFalse = in15_
                    index = in16_
                    raise _dafny.TailCall()
                elif True:
                    in17_ = xs
                    in18_ = f
                    in19_ = cTrue
                    in20_ = (cFalse) | (_dafny.Set({(xs)[index]}))
                    in21_ = (index) + (1)
                    xs = in17_
                    f = in18_
                    cTrue = in19_
                    cFalse = in20_
                    index = in21_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SplitSeq(xs, f):
        if (len(xs)) == (0):
            return (_dafny.Set({}), _dafny.Set({}))
        elif True:
            d_13_r_ = default__.SplitSeq(_dafny.SeqWithoutIsStrInference((xs)[1::]), f)
            if f((xs)[0]):
                return (((d_13_r_)[0]) | (_dafny.Set({(xs)[0]})), (d_13_r_)[1])
            elif True:
                return ((d_13_r_)[0], ((d_13_r_)[1]) | (_dafny.Set({(xs)[0]})))

