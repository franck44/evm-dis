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

# Module: Automata


class ValidAuto:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({}))

class Auto:
    @classmethod
    def default(cls, ):
        return lambda: Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.Seq({}), _dafny.Map({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Auto(self) -> bool:
        return isinstance(self, Auto_Auto)
    def Equals(self, b):
        return (((self).transitionsNat) == ((b).transitionsNat)) and (((self).states) == ((b).states))

    def AddState(self, i):
        if (i) in ((self).states):
            return self
        elif True:
            d_0_dt__update__tmp_h0_ = self
            d_1_dt__update_hrevTransitionsNat_h0_ = ((self).revTransitionsNat).set(len((self).states), _dafny.SeqWithoutIsStrInference([]))
            d_2_dt__update_htransitionsNat_h0_ = ((self).transitionsNat).set(len((self).states), _dafny.SeqWithoutIsStrInference([]))
            d_3_dt__update_hindexOf_h0_ = ((self).indexOf).set(i, len((self).states))
            d_4_dt__update_hstates_h0_ = ((self).states) + (_dafny.SeqWithoutIsStrInference([i]))
            return Auto_Auto(d_2_dt__update_htransitionsNat_h0_, d_1_dt__update_hrevTransitionsNat_h0_, d_4_dt__update_hstates_h0_, d_3_dt__update_hindexOf_h0_)

    def AddStates(self, xs):
        _this = self
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return _this
                elif True:
                    in0_ = (_this).AddState((xs)[0])
                    in1_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    _this = in0_
                    
                    xs = in1_
                    raise _dafny.TailCall()
                break

    def AddEdge(self, i, j):
        pat_let_tv0_ = j
        pat_let_tv1_ = i
        pat_let_tv2_ = i
        pat_let_tv3_ = j
        d_0_a1_ = ((self).AddState(i)).AddState(j)
        if (((d_0_a1_).indexOf)[j]) in (((d_0_a1_).transitionsNat)[((d_0_a1_).indexOf)[i]]):
            return d_0_a1_
        elif True:
            def iife0_(_pat_let0_0):
                def iife1_(d_2_dt__update__tmp_h0_):
                    def iife2_(_pat_let1_0):
                        def iife3_(d_3_dt__update_hrevTransitionsNat_h0_):
                            def iife4_(_pat_let2_0):
                                def iife5_(d_4_dt__update_htransitionsNat_h0_):
                                    return Auto_Auto(d_4_dt__update_htransitionsNat_h0_, d_3_dt__update_hrevTransitionsNat_h0_, (d_2_dt__update__tmp_h0_).states, (d_2_dt__update__tmp_h0_).indexOf)
                                return iife5_(_pat_let2_0)
                            return iife4_(MiscTypes.default__.AddKeyVal((d_0_a1_).transitionsNat, ((d_0_a1_).indexOf)[pat_let_tv2_], ((d_0_a1_).indexOf)[pat_let_tv3_]))
                        return iife3_(_pat_let1_0)
                    return iife2_(MiscTypes.default__.AddKeyVal((d_0_a1_).revTransitionsNat, ((d_0_a1_).indexOf)[pat_let_tv0_], ((d_0_a1_).indexOf)[pat_let_tv1_]))
                return iife1_(_pat_let0_0)
            d_1_w_ = iife0_(d_0_a1_)
            return d_1_w_

    def AddEdges(self, i, js, index):
        if (len(js)) == (index):
            return (self).AddState(i)
        elif True:
            d_0_a1_ = (self).AddEdge(i, (js)[index])
            d_1_a2_ = (d_0_a1_).AddEdges(i, js, (index) + (1))
            return d_1_a2_

    def SSize(self):
        return len((self).states)

    def TSize(self, index):
        d_0___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (index) == (len((_this).states)):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (len(((_this).transitionsNat)[index]))
                    in0_ = _this
                    in1_ = (index) + (1)
                    _this = in0_
                    
                    index = in1_
                    raise _dafny.TailCall()
                break

    def Succ(self, s):
        return _dafny.SeqWithoutIsStrInference([((self).states)[(((self).transitionsNat)[((self).indexOf)[s]])[d_0_i_]] for d_0_i_ in range(len(((self).transitionsNat)[((self).indexOf)[s]]))])

    def SuccNat(self, i):
        return ((self).transitionsNat)[i]

    def PredNat(self, i):
        return ((self).revTransitionsNat)[i]

    def ToDot(self, nodeToString, labelToString, prefix, name):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Number of states: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of((self).SSize()))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// Number of transitions : "))).VerbatimString(False))
        _dafny.print(_dafny.string_of((self).TSize(0)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph G {\n"))).VerbatimString(False))
        _dafny.print((prefix).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        hi0_ = len((self).states)
        for d_0_i_ in range(0, hi0_):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s_"))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_0_i_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [label="))).VerbatimString(False))
            _dafny.print(((nodeToString(((self).states)[d_0_i_], d_0_i_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))).VerbatimString(False))
        hi1_ = len((self).states)
        for d_1_i_ in range(0, hi1_):
            hi2_ = len(((self).transitionsNat)[d_1_i_])
            for d_2_j_ in range(0, hi2_):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s_"))).VerbatimString(False))
                _dafny.print(_dafny.string_of(d_1_i_))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> "))).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s_"))).VerbatimString(False))
                _dafny.print(_dafny.string_of((((self).transitionsNat)[d_1_i_])[d_2_j_]))
                _dafny.print((labelToString(((self).states)[d_1_i_], d_2_j_, ((self).states)[(((self).transitionsNat)[d_1_i_])[d_2_j_]])).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ";\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))


class Auto_Auto(Auto, NamedTuple('Auto', [('transitionsNat', Any), ('revTransitionsNat', Any), ('states', Any), ('indexOf', Any)])):
    def __dafnystr__(self) -> str:
        return f'Automata.Auto.Auto({_dafny.string_of(self.transitionsNat)}, {_dafny.string_of(self.revTransitionsNat)}, {_dafny.string_of(self.states)}, {_dafny.string_of(self.indexOf)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Auto_Auto) and self.transitionsNat == __o.transitionsNat and self.revTransitionsNat == __o.revTransitionsNat and self.states == __o.states and self.indexOf == __o.indexOf
    def __hash__(self) -> int:
        return super().__hash__()

