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

# Module: Automata


class ValidAuto:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Auto_Auto(_dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({}))

class Auto:
    @classmethod
    def default(cls, ):
        return lambda: Auto_Auto(_dafny.Map({}), _dafny.Seq({}), _dafny.Map({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Auto(self) -> bool:
        return isinstance(self, Auto_Auto)
    def Equals(self, b):
        return (((self).transitionsNat) == ((b).transitionsNat)) and (((self).states) == ((b).states))

    def AddState(self, i):
        pat_let_tv0_ = i
        pat_let_tv1_ = i
        if (i) in ((self).states):
            return self
        elif True:
            def iife1_(_pat_let1_0):
                def iife2_(d_804_dt__update__tmp_h0_):
                    def iife3_(_pat_let2_0):
                        def iife4_(d_805_dt__update_hstates_h0_):
                            return Auto_Auto((d_804_dt__update__tmp_h0_).transitionsNat, d_805_dt__update_hstates_h0_, (d_804_dt__update__tmp_h0_).indexOf)
                        return iife4_(_pat_let2_0)
                    return iife3_(((self).states) + (_dafny.SeqWithoutIsStrInference([pat_let_tv0_])))
                return iife2_(_pat_let1_0)
            def iife0_(_pat_let0_0):
                def iife5_(d_806_dt__update__tmp_h1_):
                    def iife6_(_pat_let3_0):
                        def iife7_(d_807_dt__update_hindexOf_h0_):
                            return Auto_Auto((d_806_dt__update__tmp_h1_).transitionsNat, (d_806_dt__update__tmp_h1_).states, d_807_dt__update_hindexOf_h0_)
                        return iife7_(_pat_let3_0)
                    return iife6_(((self).indexOf) | (_dafny.Map({pat_let_tv1_: len((self).states)})))
                return iife5_(_pat_let0_0)
            d_803_dt__update__tmp_h3_ = iife0_(iife1_(self))
            d_808_dt__update_htransitionsNat_h0_ = ((self).transitionsNat) | (_dafny.Map({len((self).states): _dafny.SeqWithoutIsStrInference([])}))
            return Auto_Auto(d_808_dt__update_htransitionsNat_h0_, (d_803_dt__update__tmp_h3_).states, (d_803_dt__update__tmp_h3_).indexOf)

    def AddStates(self, xs):
        _this = self
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return _this
                elif True:
                    in84_ = (_this).AddState((xs)[0])
                    in85_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    _this = in84_
                    
                    xs = in85_
                    raise _dafny.TailCall()
                break

    def AddEdge(self, i, j):
        pat_let_tv2_ = i
        pat_let_tv3_ = i
        pat_let_tv4_ = j
        d_809_a1_ = ((self).AddState(i)).AddState(j)
        if (((d_809_a1_).indexOf)[j]) in (((d_809_a1_).transitionsNat)[((d_809_a1_).indexOf)[i]]):
            return d_809_a1_
        elif True:
            def iife8_(_pat_let4_0):
                def iife9_(d_811_dt__update__tmp_h1_):
                    def iife10_(_pat_let5_0):
                        def iife11_(d_812_dt__update_htransitionsNat_h0_):
                            return Auto_Auto(d_812_dt__update_htransitionsNat_h0_, (d_811_dt__update__tmp_h1_).states, (d_811_dt__update__tmp_h1_).indexOf)
                        return iife11_(_pat_let5_0)
                    return iife10_(((d_809_a1_).transitionsNat) | (_dafny.Map({((d_809_a1_).indexOf)[pat_let_tv2_]: (((d_809_a1_).transitionsNat)[((d_809_a1_).indexOf)[pat_let_tv3_]]) + (_dafny.SeqWithoutIsStrInference([((d_809_a1_).indexOf)[pat_let_tv4_]]))})))
                return iife9_(_pat_let4_0)
            d_810_w_ = iife8_(d_809_a1_)
            return d_810_w_

    def AddEdges(self, i, js, index):
        if (len(js)) == (index):
            return (self).AddState(i)
        elif True:
            d_813_a1_ = (self).AddEdge(i, (js)[index])
            d_814_a2_ = (d_813_a1_).AddEdges(i, js, (index) + (1))
            return d_814_a2_

    def SSize(self):
        return len((self).states)

    def TSize(self, index):
        d_815___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (index) == (len((_this).states)):
                    return (0) + (d_815___accumulator_)
                elif True:
                    d_815___accumulator_ = (d_815___accumulator_) + (len(((_this).transitionsNat)[index]))
                    in86_ = _this
                    in87_ = (index) + (1)
                    _this = in86_
                    
                    index = in87_
                    raise _dafny.TailCall()
                break

    def Succ(self, s):
        return _dafny.SeqWithoutIsStrInference([((self).states)[(((self).transitionsNat)[((self).indexOf)[s]])[d_816_i_]] for d_816_i_ in range(len(((self).transitionsNat)[((self).indexOf)[s]]))])

    def SuccNat(self, i):
        return ((self).transitionsNat)[i]

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
        for d_817_i_ in range(0, hi0_):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s_"))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_817_i_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [label="))).VerbatimString(False))
            _dafny.print(((nodeToString(((self).states)[d_817_i_])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))).VerbatimString(False))
        hi1_ = len((self).states)
        for d_818_i_ in range(0, hi1_):
            hi2_ = len(((self).transitionsNat)[d_818_i_])
            for d_819_j_ in range(0, hi2_):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s_"))).VerbatimString(False))
                _dafny.print(_dafny.string_of(d_818_i_))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> "))).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s_"))).VerbatimString(False))
                _dafny.print(_dafny.string_of((((self).transitionsNat)[d_818_i_])[d_819_j_]))
                _dafny.print((labelToString(((self).states)[d_818_i_], d_819_j_, ((self).states)[(((self).transitionsNat)[d_818_i_])[d_819_j_]])).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ";\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n"))).VerbatimString(False))


class Auto_Auto(Auto, NamedTuple('Auto', [('transitionsNat', Any), ('states', Any), ('indexOf', Any)])):
    def __dafnystr__(self) -> str:
        return f'Automata.Auto.Auto({_dafny.string_of(self.transitionsNat)}, {_dafny.string_of(self.states)}, {_dafny.string_of(self.indexOf)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Auto_Auto) and self.transitionsNat == __o.transitionsNat and self.states == __o.states and self.indexOf == __o.indexOf
    def __hash__(self) -> int:
        return super().__hash__()

