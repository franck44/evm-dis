import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import MiscTypes as MiscTypes
import Int as Int
import EVMConstants as EVMConstants
import EVMOpcodes as EVMOpcodes
import OpcodeDecoder as OpcodeDecoder
import Hex as Hex
import StackElement as StackElement
import WeakPre as WeakPre
import State as State
import EVMToolTips as EVMToolTips
import Instructions as Instructions
import BinaryDecoder as BinaryDecoder
import LinSegments as LinSegments
import Splitter as Splitter
import SegBuilder as SegBuilder
import CFGState as CFGState
import ProofObject as ProofObject
import PrettyIns as PrettyIns
import PrettyPrinters as PrettyPrinters
import Automata as Automata

# Module: SeqOfSets

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SetU(xs):
        d_0___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.Set({})) | (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) | ((xs)[0])
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in0_
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
        d_0_asSeq_ = default__.SetToSequence(xs)
        return default__.SplitSeqTail(d_0_asSeq_, f, _dafny.Set({}), _dafny.Set({}), 0)

    @staticmethod
    def SplitSeqOfSet(xs, f):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([default__.SplitSet((xs)[0], f)]))
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in1_ = f
                    xs = in0_
                    f = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetToSequence(s):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv0_ = s
                if (s) == (_dafny.Set({})):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife0_(_let_dummy_3):
                        d_1_x_: int = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: int
                            for assign_such_that_0_ in (s).Elements:
                                d_1_x_ = assign_such_that_0_
                                if System_.nat._Is(d_1_x_):
                                    def lambda0_(forall_var_0_):
                                        d_2_y_: int = forall_var_0_
                                        if System_.nat._Is(d_2_y_):
                                            return not ((d_2_y_) in (s)) or ((d_1_x_) <= (d_2_y_))
                                        elif True:
                                            return True

                                    if ((d_1_x_) in (s)) and (_dafny.quantifier((s).Elements, True, lambda0_)):
                                        raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value")
                            pass
                        return (_dafny.SeqWithoutIsStrInference([d_1_x_])) + (default__.SetToSequence((pat_let_tv0_) - (_dafny.Set({d_1_x_}))))
                    return iife0_(0)
                    
                break

    @staticmethod
    def SplitSeqTail(xs, f, cTrue, cFalse, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return (cTrue, cFalse)
                elif f((xs)[index]):
                    in0_ = xs
                    in1_ = f
                    in2_ = (cTrue) | (_dafny.Set({(xs)[index]}))
                    in3_ = cFalse
                    in4_ = (index) + (1)
                    xs = in0_
                    f = in1_
                    cTrue = in2_
                    cFalse = in3_
                    index = in4_
                    raise _dafny.TailCall()
                elif True:
                    in5_ = xs
                    in6_ = f
                    in7_ = cTrue
                    in8_ = (cFalse) | (_dafny.Set({(xs)[index]}))
                    in9_ = (index) + (1)
                    xs = in5_
                    f = in6_
                    cTrue = in7_
                    cFalse = in8_
                    index = in9_
                    raise _dafny.TailCall()
                break

