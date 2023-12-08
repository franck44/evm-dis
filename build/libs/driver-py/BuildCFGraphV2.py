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
import ProofObjectBuilder
import ArgParser
import SeqOfSets
import PartitionMod
import Automata
import Minimiser
import CFGraph
import LoopResolver

# Module: BuildCFGraphV2

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BuildCFGV6(c, maxDepth, numSeg, s, h, stat):
        pat_let_tv2_ = h
        pat_let_tv3_ = numSeg
        pat_let_tv4_ = h
        pat_let_tv5_ = h
        pat_let_tv6_ = stat
        pat_let_tv7_ = h
        pat_let_tv8_ = c
        pat_let_tv9_ = h
        pat_let_tv10_ = numSeg
        pat_let_tv11_ = h
        pat_let_tv12_ = h
        pat_let_tv13_ = h
        pat_let_tv14_ = h
        pat_let_tv15_ = h
        pat_let_tv16_ = c
        pat_let_tv17_ = maxDepth
        pat_let_tv18_ = stat
        pat_let_tv19_ = h
        pat_let_tv20_ = numSeg
        pat_let_tv21_ = h
        pat_let_tv22_ = h
        pat_let_tv23_ = stat
        pat_let_tv24_ = h
        pat_let_tv25_ = numSeg
        pat_let_tv26_ = h
        pat_let_tv27_ = h
        pat_let_tv28_ = stat
        pat_let_tv29_ = c
        pat_let_tv30_ = h
        pat_let_tv31_ = numSeg
        pat_let_tv32_ = h
        pat_let_tv33_ = numSeg
        pat_let_tv34_ = h
        pat_let_tv35_ = h
        pat_let_tv36_ = h
        pat_let_tv37_ = h
        pat_let_tv38_ = c
        pat_let_tv39_ = maxDepth
        pat_let_tv40_ = h
        pat_let_tv41_ = h
        pat_let_tv42_ = numSeg
        pat_let_tv43_ = h
        pat_let_tv44_ = h
        pat_let_tv45_ = h
        pat_let_tv46_ = h
        pat_let_tv47_ = c
        pat_let_tv48_ = maxDepth
        pat_let_tv49_ = h
        pat_let_tv50_ = numSeg
        pat_let_tv51_ = c
        pat_let_tv52_ = c
        pat_let_tv53_ = h
        pat_let_tv54_ = h
        pat_let_tv55_ = c
        pat_let_tv56_ = h
        pat_let_tv57_ = numSeg
        pat_let_tv58_ = h
        pat_let_tv59_ = h
        pat_let_tv60_ = numSeg
        pat_let_tv61_ = h
        if (not((((c).xs)[numSeg]).HasExit(False))) and (not((((c).xs)[numSeg]).HasExit(True))):
            return (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), (h).seenStates), stat)
        elif (maxDepth) == (0):
            return (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((h).path, MiscTypes.Option_Some(numSeg)), True, CFGraph.CFGNode_CFGNode((h).path, MiscTypes.Option_Some(numSeg)))]), (len((c).xs)) - (1)), (h).seenStates), (stat).SetMaxDepth())
        elif True:
            def iife37_(_pat_let18_0):
                def iife38_(d_1004_leftSucc_):
                    def iife39_(_pat_let19_0):
                        def iife40_(d_1005_nextSeg_):
                            def iife41_(_pat_let20_0):
                                def iife42_(d_1006_src_):
                                    def iife43_(_pat_let21_0):
                                        def iife44_(d_1007_tgt_):
                                            def iife45_(_pat_let22_0):
                                                def iife46_(d_1008_newSeenSegs_):
                                                    def iife47_(_pat_let23_0):
                                                        def iife48_(d_1009_h1_):
                                                            def iife49_(_pat_let24_0):
                                                                def iife50_(d_1010_gleft_):
                                                                    return (CFGComputation_CFGComputation((((d_1010_gleft_)[0]).grph).AddEdge(CFGraph.BoolEdge_BoolEdge(d_1006_src_, False, d_1007_tgt_)), ((d_1010_gleft_)[0]).states), (d_1010_gleft_)[1])
                                                                return iife50_(_pat_let24_0)
                                                            return iife49_(default__.BuildCFGV6(pat_let_tv16_, (pat_let_tv17_) - (1), (d_1005_nextSeg_).v, d_1004_leftSucc_, d_1009_h1_, pat_let_tv18_))
                                                        return iife48_(_pat_let23_0)
                                                    return iife47_(History_History(((pat_let_tv13_).seen) + (_dafny.SeqWithoutIsStrInference([d_1007_tgt_])), ((pat_let_tv14_).seenPCs) + (_dafny.SeqWithoutIsStrInference([(d_1004_leftSucc_).PC()])), ((pat_let_tv15_).path) + (_dafny.SeqWithoutIsStrInference([False])), d_1008_newSeenSegs_))
                                                return iife46_(_pat_let22_0)
                                            return iife45_(((pat_let_tv12_).seenStates).set(d_1004_leftSucc_, d_1007_tgt_))
                                        return iife44_(_pat_let21_0)
                                    return iife43_(CFGraph.CFGNode_CFGNode(((pat_let_tv11_).path) + (_dafny.SeqWithoutIsStrInference([False])), d_1005_nextSeg_))
                                return iife42_(_pat_let20_0)
                            return (iife41_(CFGraph.CFGNode_CFGNode((pat_let_tv9_).path, MiscTypes.Option_Some(pat_let_tv10_))) if (d_1005_nextSeg_).is_Some else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv19_).path, MiscTypes.Option_Some(pat_let_tv20_)), False, CFGraph.CFGNode_CFGNode(((pat_let_tv21_).path) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0), (pat_let_tv22_).seenStates), pat_let_tv23_))
                        return iife40_(_pat_let19_0)
                    return ((CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv2_).path, MiscTypes.Option_Some(pat_let_tv3_)), False, ((pat_let_tv4_).seenStates)[d_1004_leftSucc_])]), 0), (pat_let_tv5_).seenStates), (pat_let_tv6_).IncFound()) if (d_1004_leftSucc_) in ((pat_let_tv7_).seenStates) else (iife39_(LinSegments.default__.PCToSeg((pat_let_tv8_).xs, (d_1004_leftSucc_).PC(), 0)) if ((d_1004_leftSucc_).is_EState) and (((d_1004_leftSucc_).PC()) < (Int.default__.TWO__256)) else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv24_).path, MiscTypes.Option_Some(pat_let_tv25_)), False, CFGraph.CFGNode_CFGNode(((pat_let_tv26_).path) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0), (pat_let_tv27_).seenStates), pat_let_tv28_)))
                return iife38_(_pat_let18_0)
            d_1003_leftBranch_ = (iife37_((((c).xs)[numSeg]).Run(s, False, (c).jumpDests)) if (((c).xs)[numSeg]).HasExit(False) else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), (h).seenStates), stat))
            d_1011_newSeenStates_ = ((d_1003_leftBranch_)[0]).states
            d_1012_leftStats_ = (d_1003_leftBranch_)[1]
            def iife51_(_pat_let25_0):
                def iife52_(d_1014_rightSucc_):
                    def iife53_(_pat_let26_0):
                        def iife54_(d_1015_nextSeg_):
                            def iife55_(_pat_let27_0):
                                def iife56_(d_1016_src_):
                                    def iife57_(_pat_let28_0):
                                        def iife58_(d_1017_tgt_):
                                            def iife59_(_pat_let29_0):
                                                def iife60_(d_1018_newSeenSegs_):
                                                    def iife61_(_pat_let30_0):
                                                        def iife62_(d_1019_h1_):
                                                            def iife63_(_pat_let31_0):
                                                                def iife64_(d_1020_gright_):
                                                                    return (CFGComputation_CFGComputation((((d_1020_gright_)[0]).grph).AddEdge(CFGraph.BoolEdge_BoolEdge(d_1016_src_, True, d_1017_tgt_)), ((d_1020_gright_)[0]).states), (d_1020_gright_)[1])
                                                                return iife64_(_pat_let31_0)
                                                            return iife63_(default__.BuildCFGV6(pat_let_tv38_, (pat_let_tv39_) - (1), (d_1015_nextSeg_).v, d_1014_rightSucc_, d_1019_h1_, d_1012_leftStats_))
                                                        return iife62_(_pat_let30_0)
                                                    return iife61_(History_History(((pat_let_tv35_).seen) + (_dafny.SeqWithoutIsStrInference([d_1017_tgt_])), ((pat_let_tv36_).seenPCs) + (_dafny.SeqWithoutIsStrInference([(d_1014_rightSucc_).PC()])), ((pat_let_tv37_).path) + (_dafny.SeqWithoutIsStrInference([True])), d_1018_newSeenSegs_))
                                                return iife60_(_pat_let29_0)
                                            return iife59_((d_1011_newSeenStates_).set(d_1014_rightSucc_, d_1017_tgt_))
                                        return iife58_(_pat_let28_0)
                                    return iife57_(CFGraph.CFGNode_CFGNode(((pat_let_tv34_).path) + (_dafny.SeqWithoutIsStrInference([True])), d_1015_nextSeg_))
                                return iife56_(_pat_let27_0)
                            def lambda61_(source71_):
                                if source71_.is_None:
                                    def iife65_(_pat_let32_0):
                                        def iife66_(d_1021_src_):
                                            def iife67_(_pat_let33_0):
                                                def iife68_(d_1022_tgt_):
                                                    def iife69_(_pat_let34_0):
                                                        def iife70_(d_1023_newSeenSegs_):
                                                            def iife71_(_pat_let35_0):
                                                                def iife72_(d_1024_h1_):
                                                                    def iife73_(_pat_let36_0):
                                                                        def iife74_(d_1025_gright_):
                                                                            return (CFGComputation_CFGComputation((((d_1025_gright_)[0]).grph).AddEdge(CFGraph.BoolEdge_BoolEdge(d_1021_src_, True, d_1022_tgt_)), ((d_1025_gright_)[0]).states), (d_1025_gright_)[1])
                                                                        return iife74_(_pat_let36_0)
                                                                    return iife73_(default__.BuildCFGV6(pat_let_tv47_, (pat_let_tv48_) - (1), (d_1015_nextSeg_).v, d_1014_rightSucc_, d_1024_h1_, d_1012_leftStats_))
                                                                return iife72_(_pat_let35_0)
                                                            return iife71_(History_History(((pat_let_tv44_).seen) + (_dafny.SeqWithoutIsStrInference([d_1022_tgt_])), ((pat_let_tv45_).seenPCs) + (_dafny.SeqWithoutIsStrInference([(d_1014_rightSucc_).PC()])), ((pat_let_tv46_).path) + (_dafny.SeqWithoutIsStrInference([True])), d_1023_newSeenSegs_))
                                                        return iife70_(_pat_let34_0)
                                                    return iife69_((d_1011_newSeenStates_).set(d_1014_rightSucc_, d_1022_tgt_))
                                                return iife68_(_pat_let33_0)
                                            return iife67_(CFGraph.CFGNode_CFGNode(((pat_let_tv43_).path) + (_dafny.SeqWithoutIsStrInference([True])), d_1015_nextSeg_))
                                        return iife66_(_pat_let32_0)
                                    return iife65_(CFGraph.CFGNode_CFGNode((pat_let_tv41_).path, MiscTypes.Option_Some(pat_let_tv42_)))
                                elif True:
                                    d_1026___mcc_h0_ = source71_.v
                                    def iife75_(_pat_let37_0):
                                        def iife76_(d_1027_prev_):
                                            return (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv49_).path, MiscTypes.Option_Some(pat_let_tv50_)), True, d_1027_prev_)]), len((pat_let_tv51_).xs)), d_1011_newSeenStates_), (d_1012_leftStats_).IncWpre())
                                        return iife76_(_pat_let37_0)
                                    return iife75_(d_1026___mcc_h0_)

                            return (((CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv30_).path, MiscTypes.Option_Some(pat_let_tv31_)), True, (d_1011_newSeenStates_)[d_1014_rightSucc_])]), 0), d_1011_newSeenStates_), (d_1012_leftStats_).IncFound()) if (d_1014_rightSucc_) in (d_1011_newSeenStates_) else (iife55_(CFGraph.CFGNode_CFGNode((pat_let_tv32_).path, MiscTypes.Option_Some(pat_let_tv33_))) if ((d_1014_rightSucc_).PC()) not in ((pat_let_tv40_).seenPCs) else lambda61_(LoopResolver.default__.SafeLoopFound((pat_let_tv52_).xs, (d_1014_rightSucc_).PC(), (pat_let_tv53_).seen, ((pat_let_tv54_).path) + (_dafny.SeqWithoutIsStrInference([True])), (pat_let_tv55_).jumpDests)))) if (d_1015_nextSeg_).is_Some else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv56_).path, MiscTypes.Option_Some(pat_let_tv57_)), True, CFGraph.CFGNode_CFGNode(((pat_let_tv58_).path) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0), d_1011_newSeenStates_), d_1012_leftStats_))
                        return iife54_(_pat_let26_0)
                    return (iife53_(LinSegments.default__.PCToSeg((pat_let_tv29_).xs, (d_1014_rightSucc_).PC(), 0)) if ((d_1014_rightSucc_).is_EState) and (((d_1014_rightSucc_).PC()) < (Int.default__.TWO__256)) else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv59_).path, MiscTypes.Option_Some(pat_let_tv60_)), True, CFGraph.CFGNode_CFGNode(((pat_let_tv61_).path) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0), d_1011_newSeenStates_), d_1012_leftStats_))
                return iife52_(_pat_let25_0)
            d_1013_rightBranch_ = (iife51_((((c).xs)[numSeg]).Run(s, True, (c).jumpDests)) if (((c).xs)[numSeg]).HasExit(True) else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), d_1011_newSeenStates_), d_1012_leftStats_))
            return (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(((((d_1003_leftBranch_)[0]).grph).edges) + ((((d_1013_rightBranch_)[0]).grph).edges), (len((c).xs)) - (1)), ((d_1013_rightBranch_)[0]).states), (d_1013_rightBranch_)[1])

    @_dafny.classproperty
    def DEFAULT__STATS(instance):
        return Stats_Stats(False, 0, 0)

class History:
    @classmethod
    def default(cls, ):
        return lambda: History_History(_dafny.Seq({}), _dafny.Seq({}), _dafny.Seq({}), _dafny.Map({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_History(self) -> bool:
        return isinstance(self, History_History)
    def IsConsistent(self, c, s):
        def lambda62_(forall_var_12_):
            d_1028_k_: int = forall_var_12_
            return not (((0) <= (d_1028_k_)) and ((d_1028_k_) < (len((self).seen)))) or (((((self).seen)[d_1028_k_]).id) == (_dafny.SeqWithoutIsStrInference(((self).path)[:d_1028_k_:])))

        def lambda63_(forall_var_13_):
            d_1029_k_: int = forall_var_13_
            return not (((0) <= (d_1029_k_)) and ((d_1029_k_) < (len((self).seen)))) or (((((self).seen)[d_1029_k_]).seg).is_Some)

        def lambda64_(forall_var_14_):
            d_1030_k_: CFGraph.CFGNode = forall_var_14_
            return not (((d_1030_k_) in ((self).seen)) and (((d_1030_k_).seg).is_Some)) or ((((d_1030_k_).seg).v) < (len((c).xs)))

        def lambda65_(forall_var_15_):
            d_1031_k_: int = forall_var_15_
            return not (((0) <= (d_1031_k_)) and ((d_1031_k_) < (len((self).seen)))) or ((((self).seenPCs)[d_1031_k_]) == ((((c).xs)[((((self).seen)[d_1031_k_]).seg).v]).StartAddress()))

        def lambda66_(forall_var_16_):
            d_1032_s_: State.AState = forall_var_16_
            return not (((d_1032_s_) in ((self).seenStates)) and (((((self).seenStates)[d_1032_s_]).seg).is_Some)) or ((((((self).seenStates)[d_1032_s_]).seg).v) < (len((c).xs)))

        return (((((((((len((self).seen)) == (len((self).seenPCs))) and ((len((self).seenPCs)) == ((len((self).path)) + (1)))) and ((s) in ((self).seenStates))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).seen)), True, lambda62_))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).seen)), True, lambda63_))) and (_dafny.quantifier(((self).seen).UniqueElements, True, lambda64_))) and (((s).PC()) == (((self).seenPCs)[(len((self).seenPCs)) - (1)]))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).seen)), True, lambda65_))) and (_dafny.quantifier(((self).seenStates).keys.Elements, True, lambda66_))


class History_History(History, NamedTuple('History', [('seen', Any), ('seenPCs', Any), ('path', Any), ('seenStates', Any)])):
    def __dafnystr__(self) -> str:
        return f'BuildCFGraphV2.History.History({_dafny.string_of(self.seen)}, {_dafny.string_of(self.seenPCs)}, {_dafny.string_of(self.path)}, {_dafny.string_of(self.seenStates)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, History_History) and self.seen == __o.seen and self.seenPCs == __o.seenPCs and self.path == __o.path and self.seenStates == __o.seenStates
    def __hash__(self) -> int:
        return super().__hash__()


class Context:
    @classmethod
    def default(cls, ):
        return lambda: Context_Context(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Context(self) -> bool:
        return isinstance(self, Context_Context)

class Context_Context(Context, NamedTuple('Context', [('xs', Any), ('jumpDests', Any)])):
    def __dafnystr__(self) -> str:
        return f'BuildCFGraphV2.Context.Context({_dafny.string_of(self.xs)}, {_dafny.string_of(self.jumpDests)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Context_Context) and self.xs == __o.xs and self.jumpDests == __o.jumpDests
    def __hash__(self) -> int:
        return super().__hash__()


class Stats:
    @classmethod
    def default(cls, ):
        return lambda: Stats_Stats(False, int(0), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Stats(self) -> bool:
        return isinstance(self, Stats_Stats)
    def SetMaxDepth(self):
        d_1033_dt__update__tmp_h0_ = self
        d_1034_dt__update_hmaxDepthReached_h0_ = True
        return Stats_Stats(d_1034_dt__update_hmaxDepthReached_h0_, (d_1033_dt__update__tmp_h0_).statesAlreadyFound, (d_1033_dt__update__tmp_h0_).wPreInvSuccess)

    def IncFound(self):
        d_1035_dt__update__tmp_h0_ = self
        d_1036_dt__update_hstatesAlreadyFound_h0_ = ((self).statesAlreadyFound) + (1)
        return Stats_Stats((d_1035_dt__update__tmp_h0_).maxDepthReached, d_1036_dt__update_hstatesAlreadyFound_h0_, (d_1035_dt__update__tmp_h0_).wPreInvSuccess)

    def IncWpre(self):
        d_1037_dt__update__tmp_h0_ = self
        d_1038_dt__update_hwPreInvSuccess_h0_ = ((self).wPreInvSuccess) + (1)
        return Stats_Stats((d_1037_dt__update__tmp_h0_).maxDepthReached, (d_1037_dt__update__tmp_h0_).statesAlreadyFound, d_1038_dt__update_hwPreInvSuccess_h0_)

    def PrettyPrint(self):
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// MaxDepth reached:"))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if (self).maxDepthReached else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// States seen:")))) + (Int.default__.NatToString((self).statesAlreadyFound))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// WPre success:")))) + (Int.default__.NatToString((self).wPreInvSuccess))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))


class Stats_Stats(Stats, NamedTuple('Stats', [('maxDepthReached', Any), ('statesAlreadyFound', Any), ('wPreInvSuccess', Any)])):
    def __dafnystr__(self) -> str:
        return f'BuildCFGraphV2.Stats.Stats({_dafny.string_of(self.maxDepthReached)}, {_dafny.string_of(self.statesAlreadyFound)}, {_dafny.string_of(self.wPreInvSuccess)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Stats_Stats) and self.maxDepthReached == __o.maxDepthReached and self.statesAlreadyFound == __o.statesAlreadyFound and self.wPreInvSuccess == __o.wPreInvSuccess
    def __hash__(self) -> int:
        return super().__hash__()


class CFGComputation:
    @classmethod
    def default(cls, ):
        return lambda: CFGComputation_CFGComputation(CFGraph.BoolCFGraph.default()(), _dafny.Map({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CFGComputation(self) -> bool:
        return isinstance(self, CFGComputation_CFGComputation)
    def Graph(self):
        return (self).grph

    def States(self):
        return (self).states


class CFGComputation_CFGComputation(CFGComputation, NamedTuple('CFGComputation', [('grph', Any), ('states', Any)])):
    def __dafnystr__(self) -> str:
        return f'BuildCFGraphV2.CFGComputation.CFGComputation({_dafny.string_of(self.grph)}, {_dafny.string_of(self.states)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CFGComputation_CFGComputation) and self.grph == __o.grph and self.states == __o.states
    def __hash__(self) -> int:
        return super().__hash__()

