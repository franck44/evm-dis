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
import SeqOfSets

# Module: PartitionMod

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SplitAll(p, f, index, max):
        while True:
            with _dafny.label():
                if (max) == (index):
                    return p
                elif True:
                    def lambda22_(d_615_f_, d_616_max_, d_617_index_):
                        def lambda23_(d_618_x_):
                            return d_615_f_((d_618_x_) + (1))

                        return lambda23_

                    d_614_f_k_ = lambda22_(f, max, index)
                    d_619_p1_ = (p).SplitAt(f(0), 0)
                    in83_ = d_619_p1_
                    in84_ = d_614_f_k_
                    in85_ = (index) + (1)
                    in86_ = max
                    p = in83_
                    f = in84_
                    index = in85_
                    max = in86_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintPartition(p):
        hi3_ = len((p).elem)
        for d_620_k_ in range(0, hi3_):
            d_621_setToSeq_: _dafny.Seq
            d_621_setToSeq_ = SeqOfSets.default__.SetToSequence(((p).elem)[d_620_k_])
            _dafny.print(_dafny.string_of(d_621_setToSeq_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))


class ValidPartition:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Partition_Partition(1, _dafny.SeqWithoutIsStrInference([_dafny.Set({0})]))

class Partition:
    @classmethod
    def default(cls, ):
        return lambda: Partition_Partition(int(0), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Partition(self) -> bool:
        return isinstance(self, Partition_Partition)
    def SplitAt(self, f, index):
        d_622_r_ = SeqOfSets.default__.SplitSet(((self).elem)[index], f)
        if (((d_622_r_)[0]) != (_dafny.Set({}))) and (((d_622_r_)[1]) != (_dafny.Set({}))):
            d_623_j_ = ((_dafny.SeqWithoutIsStrInference(((self).elem)[:index:])) + (_dafny.SeqWithoutIsStrInference(((self).elem)[(index) + (1)::]))) + (_dafny.SeqWithoutIsStrInference([(d_622_r_)[0], (d_622_r_)[1]]))
            d_624_pp_ = Partition_Partition((self).n, d_623_j_)
            return d_624_pp_
        elif ((d_622_r_)[0]) != (_dafny.Set({})):
            d_625_j_ = ((_dafny.SeqWithoutIsStrInference(((self).elem)[:index:])) + (_dafny.SeqWithoutIsStrInference(((self).elem)[(index) + (1)::]))) + (_dafny.SeqWithoutIsStrInference([(d_622_r_)[0]]))
            return Partition_Partition((self).n, d_625_j_)
        elif True:
            d_626_j_ = ((_dafny.SeqWithoutIsStrInference(((self).elem)[:index:])) + (_dafny.SeqWithoutIsStrInference(((self).elem)[(index) + (1)::]))) + (_dafny.SeqWithoutIsStrInference([(d_622_r_)[1]]))
            return Partition_Partition((self).n, d_626_j_)

    def GetClass(self, x, index):
        _this = self
        while True:
            with _dafny.label():
                if (x) in (((_this).elem)[index]):
                    return index
                elif True:
                    in87_ = _this
                    in88_ = x
                    in89_ = (index) + (1)
                    _this = in87_
                    
                    x = in88_
                    index = in89_
                    raise _dafny.TailCall()
                break

    def Equiv(self, x, y):
        return ((self).GetClass(x, 0)) == ((self).GetClass(y, 0))

    def Refines2(self, p):
        def lambda24_(forall_var_8_):
            def lambda25_(exists_var_0_):
                d_628_c_: _dafny.Set = exists_var_0_
                return ((d_628_c_) in ((p).elem)) and ((d_627_k_).issubset(d_628_c_))

            d_627_k_: _dafny.Set = forall_var_8_
            return not ((d_627_k_) in ((self).elem)) or (_dafny.quantifier(((p).elem).UniqueElements, False, lambda25_))

        return _dafny.quantifier(((self).elem).UniqueElements, True, lambda24_)

    def Refines(self, p):
        return (True) and ((len((self).elem)) >= (len((p).elem)))


class Partition_Partition(Partition, NamedTuple('Partition', [('n', Any), ('elem', Any)])):
    def __dafnystr__(self) -> str:
        return f'PartitionMod.Partition.Partition({_dafny.string_of(self.n)}, {_dafny.string_of(self.elem)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Partition_Partition) and self.n == __o.n and self.elem == __o.elem
    def __hash__(self) -> int:
        return super().__hash__()

