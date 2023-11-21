import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes
import SeqOfSets
import PartitionMod
import Automata
import Minimiser

# Module: MinimiserTests

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Test1():
        d_52_a_: bool
        d_52_a_ = False
        d_53_b_: bool
        d_53_b_ = True
        d_54_p1_: PartitionMod.Partition
        d_54_p1_ = PartitionMod.Partition_Partition(5, _dafny.SeqWithoutIsStrInference([_dafny.Set({0, 1, 2, 3}), _dafny.Set({4})]))
        d_55_m_: _dafny.Map
        d_55_m_ = _dafny.Map({(0, False): 1, (0, True): 2, (1, False): 1, (1, True): 3, (2, False): 1, (2, True): 2, (3, False): 1, (3, True): 4, (4, False): 2, (4, True): 1})
        d_56_a1_: Automata.Auto
        d_56_a1_ = Automata.Auto_Auto(5, d_55_m_)
        d_57_vp0_: Minimiser.Pair
        d_57_vp0_ = Minimiser.Pair_Pair(d_56_a1_, d_54_p1_)
        d_58_vp1_: Minimiser.Pair
        d_58_vp1_ = (d_57_vp0_).SplitFrom(0)
        PartitionMod.default__.PrintPartition((d_58_vp1_).p)
        d_59_vp2_: Minimiser.Pair
        d_59_vp2_ = (d_58_vp1_).SplitFrom(0)
        PartitionMod.default__.PrintPartition((d_59_vp2_).p)
        d_60_a2_: Minimiser.Pair
        d_60_a2_ = Minimiser.default__.Minimise(d_57_vp0_)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimise result:\n"))).VerbatimString(False))
        PartitionMod.default__.PrintPartition((d_60_a2_).p)

    @staticmethod
    def Test3():
        d_61_p1_: PartitionMod.Partition
        d_61_p1_ = PartitionMod.Partition_Partition(5, _dafny.SeqWithoutIsStrInference([_dafny.Set({0, 1, 3, 2}), _dafny.Set({4})]))
        d_62_m_: _dafny.Map
        d_62_m_ = _dafny.Map({(0, False): 0})
        d_63_a1_: Automata.Auto
        d_63_a1_ = Automata.Auto_Auto(5, d_62_m_)
        d_64_vp0_: Minimiser.Pair
        d_64_vp0_ = Minimiser.Pair_Pair(d_63_a1_, d_61_p1_)
        d_65_vp1_: Minimiser.Pair
        d_65_vp1_ = (d_64_vp0_).SplitFrom(0)
        PartitionMod.default__.PrintPartition((d_65_vp1_).p)
        d_66_vp2_: Minimiser.Pair
        d_66_vp2_ = (d_65_vp1_).SplitFrom(0)
        PartitionMod.default__.PrintPartition((d_66_vp2_).p)
        d_67_a2_: Minimiser.Pair
        d_67_a2_ = Minimiser.default__.Minimise(d_64_vp0_)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimise result:\n"))).VerbatimString(False))
        PartitionMod.default__.PrintPartition((d_67_a2_).p)
        d_68_a3_: Minimiser.Pair
        d_68_a3_ = (d_64_vp0_).Minimise1()
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Minimise result:\n"))).VerbatimString(False))
        PartitionMod.default__.PrintPartition((d_68_a3_).p)

    @staticmethod
    def Test8():
        d_69_p1_: PartitionMod.Partition
        d_69_p1_ = PartitionMod.Partition_Partition(5, _dafny.SeqWithoutIsStrInference([_dafny.Set({0, 1, 2, 3, 4})]))
        d_70_m_: _dafny.Map
        d_70_m_ = _dafny.Map({(0, False): 1, (0, True): 3, (1, True): 2, (3, True): 4})
        d_71_a1_: Automata.Auto
        d_71_a1_ = Automata.Auto_Auto(5, d_70_m_)
        d_72_vp0_: Minimiser.Pair
        d_72_vp0_ = Minimiser.Pair_Pair(d_71_a1_, d_69_p1_)
        d_73_vp1_: Minimiser.Pair
        d_73_vp1_ = (d_72_vp0_).SplitFrom(0)
        PartitionMod.default__.PrintPartition((d_73_vp1_).p)
        d_74_vp2_: Minimiser.Pair
        d_74_vp2_ = (d_73_vp1_).SplitFrom(0)
        PartitionMod.default__.PrintPartition((d_74_vp2_).p)

