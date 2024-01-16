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
import CFGState
import ProofObject
import PrettyIns
import PrettyPrinters
import Automata

# Module: SeqOfSets

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SetU(xs):
        d_846___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.Set({})) | (d_846___accumulator_)
                elif True:
                    d_846___accumulator_ = (d_846___accumulator_) | ((xs)[0])
                    in106_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in106_
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
        d_847_asSeq_ = default__.SetToSequence(xs)
        return default__.SplitSeqTail(d_847_asSeq_, f, _dafny.Set({}), _dafny.Set({}), 0)

    @staticmethod
    def SplitSeqOfSet(xs, f):
        d_848___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_848___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_848___accumulator_ = (d_848___accumulator_) + (_dafny.SeqWithoutIsStrInference([default__.SplitSet((xs)[0], f)]))
                    in107_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in108_ = f
                    xs = in107_
                    f = in108_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetToSequence(s):
        d_849___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv4_ = s
                if (s) == (_dafny.Set({})):
                    return (d_849___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife6_(_let_dummy_3):
                        d_850_x_: int = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: int
                            for assign_such_that_0_ in (s).Elements:
                                d_850_x_ = assign_such_that_0_
                                def lambda41_(forall_var_9_):
                                    d_851_y_: int = forall_var_9_
                                    return not ((d_851_y_) in (s)) or ((d_850_x_) <= (d_851_y_))

                                if ((d_850_x_) in (s)) and (_dafny.quantifier((s).Elements, True, lambda41_)):
                                    raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value (line 218)")
                            pass
                        return (_dafny.SeqWithoutIsStrInference([d_850_x_])) + (default__.SetToSequence((pat_let_tv4_) - (_dafny.Set({d_850_x_}))))
                    return iife6_(0)
                    
                break

    @staticmethod
    def SplitSeqTail(xs, f, cTrue, cFalse, index):
        while True:
            with _dafny.label():
                if (len(xs)) == (index):
                    return (cTrue, cFalse)
                elif f((xs)[index]):
                    in109_ = xs
                    in110_ = f
                    in111_ = (cTrue) | (_dafny.Set({(xs)[index]}))
                    in112_ = cFalse
                    in113_ = (index) + (1)
                    xs = in109_
                    f = in110_
                    cTrue = in111_
                    cFalse = in112_
                    index = in113_
                    raise _dafny.TailCall()
                elif True:
                    in114_ = xs
                    in115_ = f
                    in116_ = cTrue
                    in117_ = (cFalse) | (_dafny.Set({(xs)[index]}))
                    in118_ = (index) + (1)
                    xs = in114_
                    f = in115_
                    cTrue = in116_
                    cFalse = in117_
                    index = in118_
                    raise _dafny.TailCall()
                break

