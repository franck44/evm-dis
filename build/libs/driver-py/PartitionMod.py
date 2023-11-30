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
import WeakPre
import State
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
                    def lambda37_(d_794_f_, d_795_max_, d_796_index_):
                        def lambda38_(d_797_x_):
                            return d_794_f_((d_797_x_) + (1))

                        return lambda38_

                    d_793_f_k_ = lambda37_(f, max, index)
                    d_798_p1_ = (p).SplitAt(f(0), 0)
                    in101_ = d_798_p1_
                    in102_ = d_793_f_k_
                    in103_ = (index) + (1)
                    in104_ = max
                    p = in101_
                    f = in102_
                    index = in103_
                    max = in104_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintPartition(p):
        hi3_ = len((p).elem)
        for d_799_k_ in range(0, hi3_):
            d_800_setToSeq_: _dafny.Seq
            d_800_setToSeq_ = SeqOfSets.default__.SetToSequence(((p).elem)[d_799_k_])
            _dafny.print(_dafny.string_of(d_800_setToSeq_))
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
        d_801_r_ = SeqOfSets.default__.SplitSet(((self).elem)[index], f)
        if (((d_801_r_)[0]) != (_dafny.Set({}))) and (((d_801_r_)[1]) != (_dafny.Set({}))):
            d_802_j_ = ((_dafny.SeqWithoutIsStrInference(((self).elem)[:index:])) + (_dafny.SeqWithoutIsStrInference(((self).elem)[(index) + (1)::]))) + (_dafny.SeqWithoutIsStrInference([(d_801_r_)[0], (d_801_r_)[1]]))
            d_803_pp_ = Partition_Partition((self).n, d_802_j_)
            return d_803_pp_
        elif ((d_801_r_)[0]) != (_dafny.Set({})):
            d_804_j_ = ((_dafny.SeqWithoutIsStrInference(((self).elem)[:index:])) + (_dafny.SeqWithoutIsStrInference(((self).elem)[(index) + (1)::]))) + (_dafny.SeqWithoutIsStrInference([(d_801_r_)[0]]))
            return Partition_Partition((self).n, d_804_j_)
        elif True:
            d_805_j_ = ((_dafny.SeqWithoutIsStrInference(((self).elem)[:index:])) + (_dafny.SeqWithoutIsStrInference(((self).elem)[(index) + (1)::]))) + (_dafny.SeqWithoutIsStrInference([(d_801_r_)[1]]))
            return Partition_Partition((self).n, d_805_j_)

    def GetClass(self, x, index):
        _this = self
        while True:
            with _dafny.label():
                if (x) in (((_this).elem)[index]):
                    return index
                elif True:
                    in105_ = _this
                    in106_ = x
                    in107_ = (index) + (1)
                    _this = in105_
                    
                    x = in106_
                    index = in107_
                    raise _dafny.TailCall()
                break

    def Equiv(self, x, y):
        return ((self).GetClass(x, 0)) == ((self).GetClass(y, 0))

    def Refines2(self, p):
        def lambda39_(forall_var_8_):
            def lambda40_(exists_var_0_):
                d_807_c_: _dafny.Set = exists_var_0_
                return ((d_807_c_) in ((p).elem)) and ((d_806_k_).issubset(d_807_c_))

            d_806_k_: _dafny.Set = forall_var_8_
            return not ((d_806_k_) in ((self).elem)) or (_dafny.quantifier(((p).elem).UniqueElements, False, lambda40_))

        return _dafny.quantifier(((self).elem).UniqueElements, True, lambda39_)

    def Refines(self, p):
        return (True) and ((len((self).elem)) >= (len((p).elem)))


class Partition_Partition(Partition, NamedTuple('Partition', [('n', Any), ('elem', Any)])):
    def __dafnystr__(self) -> str:
        return f'PartitionMod.Partition.Partition({_dafny.string_of(self.n)}, {_dafny.string_of(self.elem)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Partition_Partition) and self.n == __o.n and self.elem == __o.elem
    def __hash__(self) -> int:
        return super().__hash__()

