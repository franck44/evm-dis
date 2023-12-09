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
import EVMObject
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
        pat_let_tv1_ = h
        pat_let_tv2_ = numSeg
        pat_let_tv3_ = h
        pat_let_tv4_ = h
        pat_let_tv5_ = stat
        pat_let_tv6_ = h
        pat_let_tv7_ = c
        pat_let_tv8_ = h
        pat_let_tv9_ = numSeg
        pat_let_tv10_ = h
        pat_let_tv11_ = h
        pat_let_tv12_ = h
        pat_let_tv13_ = h
        pat_let_tv14_ = h
        pat_let_tv15_ = c
        pat_let_tv16_ = maxDepth
        pat_let_tv17_ = stat
        pat_let_tv18_ = h
        pat_let_tv19_ = numSeg
        pat_let_tv20_ = h
        pat_let_tv21_ = h
        pat_let_tv22_ = stat
        pat_let_tv23_ = h
        pat_let_tv24_ = numSeg
        pat_let_tv25_ = h
        pat_let_tv26_ = h
        pat_let_tv27_ = stat
        pat_let_tv28_ = c
        pat_let_tv29_ = h
        pat_let_tv30_ = numSeg
        pat_let_tv31_ = h
        pat_let_tv32_ = numSeg
        pat_let_tv33_ = h
        pat_let_tv34_ = h
        pat_let_tv35_ = h
        pat_let_tv36_ = h
        pat_let_tv37_ = c
        pat_let_tv38_ = maxDepth
        pat_let_tv39_ = h
        pat_let_tv40_ = h
        pat_let_tv41_ = numSeg
        pat_let_tv42_ = h
        pat_let_tv43_ = h
        pat_let_tv44_ = h
        pat_let_tv45_ = h
        pat_let_tv46_ = c
        pat_let_tv47_ = maxDepth
        pat_let_tv48_ = h
        pat_let_tv49_ = numSeg
        pat_let_tv50_ = c
        pat_let_tv51_ = c
        pat_let_tv52_ = h
        pat_let_tv53_ = h
        pat_let_tv54_ = c
        pat_let_tv55_ = h
        pat_let_tv56_ = numSeg
        pat_let_tv57_ = h
        pat_let_tv58_ = h
        pat_let_tv59_ = numSeg
        pat_let_tv60_ = h
        if (not((((c).xs)[numSeg]).HasExit(False))) and (not((((c).xs)[numSeg]).HasExit(True))):
            return (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), (h).seenStates), stat)
        elif (maxDepth) == (0):
            return (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((h).path, MiscTypes.Option_Some(numSeg)), True, CFGraph.CFGNode_CFGNode((h).path, MiscTypes.Option_Some(numSeg)))]), (len((c).xs)) - (1)), (h).seenStates), (stat).SetMaxDepth())
        elif True:
            def iife35_(_pat_let17_0):
                def iife36_(d_1007_leftSucc_):
                    def iife37_(_pat_let18_0):
                        def iife38_(d_1008_nextSeg_):
                            def iife39_(_pat_let19_0):
                                def iife40_(d_1009_src_):
                                    def iife41_(_pat_let20_0):
                                        def iife42_(d_1010_tgt_):
                                            def iife43_(_pat_let21_0):
                                                def iife44_(d_1011_newSeenSegs_):
                                                    def iife45_(_pat_let22_0):
                                                        def iife46_(d_1012_h1_):
                                                            def iife47_(_pat_let23_0):
                                                                def iife48_(d_1013_gleft_):
                                                                    return (CFGComputation_CFGComputation((((d_1013_gleft_)[0]).grph).AddEdge(CFGraph.BoolEdge_BoolEdge(d_1009_src_, False, d_1010_tgt_)), ((d_1013_gleft_)[0]).states), (d_1013_gleft_)[1])
                                                                return iife48_(_pat_let23_0)
                                                            return iife47_(default__.BuildCFGV6(pat_let_tv15_, (pat_let_tv16_) - (1), (d_1008_nextSeg_).v, d_1007_leftSucc_, d_1012_h1_, pat_let_tv17_))
                                                        return iife46_(_pat_let22_0)
                                                    return iife45_(History_History(((pat_let_tv12_).seen) + (_dafny.SeqWithoutIsStrInference([d_1010_tgt_])), ((pat_let_tv13_).seenPCs) + (_dafny.SeqWithoutIsStrInference([(d_1007_leftSucc_).PC()])), ((pat_let_tv14_).path) + (_dafny.SeqWithoutIsStrInference([False])), d_1011_newSeenSegs_))
                                                return iife44_(_pat_let21_0)
                                            return iife43_(((pat_let_tv11_).seenStates).set(d_1007_leftSucc_, d_1010_tgt_))
                                        return iife42_(_pat_let20_0)
                                    return iife41_(CFGraph.CFGNode_CFGNode(((pat_let_tv10_).path) + (_dafny.SeqWithoutIsStrInference([False])), d_1008_nextSeg_))
                                return iife40_(_pat_let19_0)
                            return (iife39_(CFGraph.CFGNode_CFGNode((pat_let_tv8_).path, MiscTypes.Option_Some(pat_let_tv9_))) if (d_1008_nextSeg_).is_Some else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv18_).path, MiscTypes.Option_Some(pat_let_tv19_)), False, CFGraph.CFGNode_CFGNode(((pat_let_tv20_).path) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0), (pat_let_tv21_).seenStates), pat_let_tv22_))
                        return iife38_(_pat_let18_0)
                    def iife49_(_pat_let24_0):
                        def iife50_(d_1014_dt__update__tmp_h0_):
                            def iife51_(_pat_let25_0):
                                def iife52_(d_1015_dt__update_herrorState_h0_):
                                    return Stats_Stats((d_1014_dt__update__tmp_h0_).maxDepthReached, (d_1014_dt__update__tmp_h0_).statesAlreadyFound, (d_1014_dt__update__tmp_h0_).wPreInvSuccess, d_1015_dt__update_herrorState_h0_)
                                return iife52_(_pat_let25_0)
                            return iife51_(True)
                        return iife50_(_pat_let24_0)
                    return ((CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv1_).path, MiscTypes.Option_Some(pat_let_tv2_)), False, ((pat_let_tv3_).seenStates)[d_1007_leftSucc_])]), 0), (pat_let_tv4_).seenStates), (pat_let_tv5_).IncFound()) if (d_1007_leftSucc_) in ((pat_let_tv6_).seenStates) else (iife37_(LinSegments.default__.PCToSeg((pat_let_tv7_).xs, (d_1007_leftSucc_).PC(), 0)) if ((d_1007_leftSucc_).is_EState) and (((d_1007_leftSucc_).PC()) < (Int.default__.TWO__256)) else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv23_).path, MiscTypes.Option_Some(pat_let_tv24_)), False, CFGraph.CFGNode_CFGNode(((pat_let_tv25_).path) + (_dafny.SeqWithoutIsStrInference([False])), MiscTypes.Option_None()))]), 0), (pat_let_tv26_).seenStates), iife49_(pat_let_tv27_))))
                return iife36_(_pat_let17_0)
            d_1006_leftBranch_ = (iife35_((((c).xs)[numSeg]).Run(s, False, (c).jumpDests)) if (((c).xs)[numSeg]).HasExit(False) else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), (h).seenStates), stat))
            d_1016_newSeenStates_ = ((d_1006_leftBranch_)[0]).states
            d_1017_leftStats_ = (d_1006_leftBranch_)[1]
            def iife53_(_pat_let26_0):
                def iife54_(d_1019_rightSucc_):
                    def iife55_(_pat_let27_0):
                        def iife56_(d_1020_nextSeg_):
                            def iife57_(_pat_let28_0):
                                def iife58_(d_1021_src_):
                                    def iife59_(_pat_let29_0):
                                        def iife60_(d_1022_tgt_):
                                            def iife61_(_pat_let30_0):
                                                def iife62_(d_1023_newSeenSegs_):
                                                    def iife63_(_pat_let31_0):
                                                        def iife64_(d_1024_h1_):
                                                            def iife65_(_pat_let32_0):
                                                                def iife66_(d_1025_gright_):
                                                                    return (CFGComputation_CFGComputation((((d_1025_gright_)[0]).grph).AddEdge(CFGraph.BoolEdge_BoolEdge(d_1021_src_, True, d_1022_tgt_)), ((d_1025_gright_)[0]).states), (d_1025_gright_)[1])
                                                                return iife66_(_pat_let32_0)
                                                            return iife65_(default__.BuildCFGV6(pat_let_tv37_, (pat_let_tv38_) - (1), (d_1020_nextSeg_).v, d_1019_rightSucc_, d_1024_h1_, d_1017_leftStats_))
                                                        return iife64_(_pat_let31_0)
                                                    return iife63_(History_History(((pat_let_tv34_).seen) + (_dafny.SeqWithoutIsStrInference([d_1022_tgt_])), ((pat_let_tv35_).seenPCs) + (_dafny.SeqWithoutIsStrInference([(d_1019_rightSucc_).PC()])), ((pat_let_tv36_).path) + (_dafny.SeqWithoutIsStrInference([True])), d_1023_newSeenSegs_))
                                                return iife62_(_pat_let30_0)
                                            return iife61_((d_1016_newSeenStates_).set(d_1019_rightSucc_, d_1022_tgt_))
                                        return iife60_(_pat_let29_0)
                                    return iife59_(CFGraph.CFGNode_CFGNode(((pat_let_tv33_).path) + (_dafny.SeqWithoutIsStrInference([True])), d_1020_nextSeg_))
                                return iife58_(_pat_let28_0)
                            def lambda67_(source71_):
                                if source71_.is_None:
                                    def iife67_(_pat_let33_0):
                                        def iife68_(d_1026_src_):
                                            def iife69_(_pat_let34_0):
                                                def iife70_(d_1027_tgt_):
                                                    def iife71_(_pat_let35_0):
                                                        def iife72_(d_1028_newSeenSegs_):
                                                            def iife73_(_pat_let36_0):
                                                                def iife74_(d_1029_h1_):
                                                                    def iife75_(_pat_let37_0):
                                                                        def iife76_(d_1030_gright_):
                                                                            return (CFGComputation_CFGComputation((((d_1030_gright_)[0]).grph).AddEdge(CFGraph.BoolEdge_BoolEdge(d_1026_src_, True, d_1027_tgt_)), ((d_1030_gright_)[0]).states), (d_1030_gright_)[1])
                                                                        return iife76_(_pat_let37_0)
                                                                    return iife75_(default__.BuildCFGV6(pat_let_tv46_, (pat_let_tv47_) - (1), (d_1020_nextSeg_).v, d_1019_rightSucc_, d_1029_h1_, d_1017_leftStats_))
                                                                return iife74_(_pat_let36_0)
                                                            return iife73_(History_History(((pat_let_tv43_).seen) + (_dafny.SeqWithoutIsStrInference([d_1027_tgt_])), ((pat_let_tv44_).seenPCs) + (_dafny.SeqWithoutIsStrInference([(d_1019_rightSucc_).PC()])), ((pat_let_tv45_).path) + (_dafny.SeqWithoutIsStrInference([True])), d_1028_newSeenSegs_))
                                                        return iife72_(_pat_let35_0)
                                                    return iife71_((d_1016_newSeenStates_).set(d_1019_rightSucc_, d_1027_tgt_))
                                                return iife70_(_pat_let34_0)
                                            return iife69_(CFGraph.CFGNode_CFGNode(((pat_let_tv42_).path) + (_dafny.SeqWithoutIsStrInference([True])), d_1020_nextSeg_))
                                        return iife68_(_pat_let33_0)
                                    return iife67_(CFGraph.CFGNode_CFGNode((pat_let_tv40_).path, MiscTypes.Option_Some(pat_let_tv41_)))
                                elif True:
                                    d_1031___mcc_h0_ = source71_.v
                                    def iife77_(_pat_let38_0):
                                        def iife78_(d_1032_prev_):
                                            return (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv48_).path, MiscTypes.Option_Some(pat_let_tv49_)), True, d_1032_prev_)]), len((pat_let_tv50_).xs)), d_1016_newSeenStates_), (d_1017_leftStats_).IncWpre())
                                        return iife78_(_pat_let38_0)
                                    return iife77_(d_1031___mcc_h0_)

                            return (((CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv29_).path, MiscTypes.Option_Some(pat_let_tv30_)), True, (d_1016_newSeenStates_)[d_1019_rightSucc_])]), 0), d_1016_newSeenStates_), (d_1017_leftStats_).IncFound()) if (d_1019_rightSucc_) in (d_1016_newSeenStates_) else (iife57_(CFGraph.CFGNode_CFGNode((pat_let_tv31_).path, MiscTypes.Option_Some(pat_let_tv32_))) if ((d_1019_rightSucc_).PC()) not in ((pat_let_tv39_).seenPCs) else lambda67_(LoopResolver.default__.SafeLoopFound((pat_let_tv51_).xs, (d_1019_rightSucc_).PC(), (pat_let_tv52_).seen, ((pat_let_tv53_).path) + (_dafny.SeqWithoutIsStrInference([True])), (pat_let_tv54_).jumpDests)))) if (d_1020_nextSeg_).is_Some else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv55_).path, MiscTypes.Option_Some(pat_let_tv56_)), True, CFGraph.CFGNode_CFGNode(((pat_let_tv57_).path) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0), d_1016_newSeenStates_), d_1017_leftStats_))
                        return iife56_(_pat_let27_0)
                    def iife79_(_pat_let39_0):
                        def iife80_(d_1033_dt__update__tmp_h1_):
                            def iife81_(_pat_let40_0):
                                def iife82_(d_1034_dt__update_herrorState_h1_):
                                    return Stats_Stats((d_1033_dt__update__tmp_h1_).maxDepthReached, (d_1033_dt__update__tmp_h1_).statesAlreadyFound, (d_1033_dt__update__tmp_h1_).wPreInvSuccess, d_1034_dt__update_herrorState_h1_)
                                return iife82_(_pat_let40_0)
                            return iife81_(True)
                        return iife80_(_pat_let39_0)
                    return (iife55_(LinSegments.default__.PCToSeg((pat_let_tv28_).xs, (d_1019_rightSucc_).PC(), 0)) if ((d_1019_rightSucc_).is_EState) and (((d_1019_rightSucc_).PC()) < (Int.default__.TWO__256)) else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([CFGraph.BoolEdge_BoolEdge(CFGraph.CFGNode_CFGNode((pat_let_tv58_).path, MiscTypes.Option_Some(pat_let_tv59_)), True, CFGraph.CFGNode_CFGNode(((pat_let_tv60_).path) + (_dafny.SeqWithoutIsStrInference([True])), MiscTypes.Option_None()))]), 0), d_1016_newSeenStates_), iife79_(d_1017_leftStats_)))
                return iife54_(_pat_let26_0)
            d_1018_rightBranch_ = (iife53_((((c).xs)[numSeg]).Run(s, True, (c).jumpDests)) if (((c).xs)[numSeg]).HasExit(True) else (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), 0), d_1016_newSeenStates_), d_1017_leftStats_))
            return (CFGComputation_CFGComputation(CFGraph.BoolCFGraph_BoolCFGraph(((((d_1006_leftBranch_)[0]).grph).edges) + ((((d_1018_rightBranch_)[0]).grph).edges), (len((c).xs)) - (1)), ((d_1018_rightBranch_)[0]).states), (d_1018_rightBranch_)[1])

    @_dafny.classproperty
    def DEFAULT__STATS(instance):
        return Stats_Stats(False, 0, 0, False)

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
        def lambda68_(forall_var_18_):
            d_1035_k_: int = forall_var_18_
            return not (((0) <= (d_1035_k_)) and ((d_1035_k_) < (len((self).seen)))) or (((((self).seen)[d_1035_k_]).id) == (_dafny.SeqWithoutIsStrInference(((self).path)[:d_1035_k_:])))

        def lambda69_(forall_var_19_):
            d_1036_k_: int = forall_var_19_
            return not (((0) <= (d_1036_k_)) and ((d_1036_k_) < (len((self).seen)))) or (((((self).seen)[d_1036_k_]).seg).is_Some)

        def lambda70_(forall_var_20_):
            d_1037_k_: CFGraph.CFGNode = forall_var_20_
            return not (((d_1037_k_) in ((self).seen)) and (((d_1037_k_).seg).is_Some)) or ((((d_1037_k_).seg).v) < (len((c).xs)))

        def lambda71_(forall_var_21_):
            d_1038_k_: int = forall_var_21_
            return not (((0) <= (d_1038_k_)) and ((d_1038_k_) < (len((self).seen)))) or ((((self).seenPCs)[d_1038_k_]) == ((((c).xs)[((((self).seen)[d_1038_k_]).seg).v]).StartAddress()))

        def lambda72_(forall_var_22_):
            d_1039_s_: State.AState = forall_var_22_
            return not (((d_1039_s_) in ((self).seenStates)) and (((((self).seenStates)[d_1039_s_]).seg).is_Some)) or ((((((self).seenStates)[d_1039_s_]).seg).v) < (len((c).xs)))

        return (((((((((len((self).seen)) == (len((self).seenPCs))) and ((len((self).seenPCs)) == ((len((self).path)) + (1)))) and ((s) in ((self).seenStates))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).seen)), True, lambda68_))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).seen)), True, lambda69_))) and (_dafny.quantifier(((self).seen).UniqueElements, True, lambda70_))) and (((s).PC()) == (((self).seenPCs)[(len((self).seenPCs)) - (1)]))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).seen)), True, lambda71_))) and (_dafny.quantifier(((self).seenStates).keys.Elements, True, lambda72_))


class History_History(History, NamedTuple('History', [('seen', Any), ('seenPCs', Any), ('path', Any), ('seenStates', Any)])):
    def __dafnystr__(self) -> str:
        return f'BuildCFGraphV2.History.History({_dafny.string_of(self.seen)}, {_dafny.string_of(self.seenPCs)}, {_dafny.string_of(self.path)}, {_dafny.string_of(self.seenStates)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, History_History) and self.seen == __o.seen and self.seenPCs == __o.seenPCs and self.path == __o.path and self.seenStates == __o.seenStates
    def __hash__(self) -> int:
        return super().__hash__()


class Stats:
    @classmethod
    def default(cls, ):
        return lambda: Stats_Stats(False, int(0), int(0), False)
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Stats(self) -> bool:
        return isinstance(self, Stats_Stats)
    def SetMaxDepth(self):
        d_1040_dt__update__tmp_h0_ = self
        d_1041_dt__update_hmaxDepthReached_h0_ = True
        return Stats_Stats(d_1041_dt__update_hmaxDepthReached_h0_, (d_1040_dt__update__tmp_h0_).statesAlreadyFound, (d_1040_dt__update__tmp_h0_).wPreInvSuccess, (d_1040_dt__update__tmp_h0_).errorState)

    def IncFound(self):
        d_1042_dt__update__tmp_h0_ = self
        d_1043_dt__update_hstatesAlreadyFound_h0_ = ((self).statesAlreadyFound) + (1)
        return Stats_Stats((d_1042_dt__update__tmp_h0_).maxDepthReached, d_1043_dt__update_hstatesAlreadyFound_h0_, (d_1042_dt__update__tmp_h0_).wPreInvSuccess, (d_1042_dt__update__tmp_h0_).errorState)

    def IncWpre(self):
        d_1044_dt__update__tmp_h0_ = self
        d_1045_dt__update_hwPreInvSuccess_h0_ = ((self).wPreInvSuccess) + (1)
        return Stats_Stats((d_1044_dt__update__tmp_h0_).maxDepthReached, (d_1044_dt__update__tmp_h0_).statesAlreadyFound, d_1045_dt__update_hwPreInvSuccess_h0_, (d_1044_dt__update__tmp_h0_).errorState)

    def PrettyPrint(self):
        return (((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// MaxDepth reached:"))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if (self).maxDepthReached else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// ErrorState reached:")))) + ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if (self).errorState else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false"))))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// States seen:")))) + (Int.default__.NatToString((self).statesAlreadyFound))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "// WPre success:")))) + (Int.default__.NatToString((self).wPreInvSuccess))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))


class Stats_Stats(Stats, NamedTuple('Stats', [('maxDepthReached', Any), ('statesAlreadyFound', Any), ('wPreInvSuccess', Any), ('errorState', Any)])):
    def __dafnystr__(self) -> str:
        return f'BuildCFGraphV2.Stats.Stats({_dafny.string_of(self.maxDepthReached)}, {_dafny.string_of(self.statesAlreadyFound)}, {_dafny.string_of(self.wPreInvSuccess)}, {_dafny.string_of(self.errorState)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Stats_Stats) and self.maxDepthReached == __o.maxDepthReached and self.statesAlreadyFound == __o.statesAlreadyFound and self.wPreInvSuccess == __o.wPreInvSuccess and self.errorState == __o.errorState
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

