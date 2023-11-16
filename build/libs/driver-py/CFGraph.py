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
import PartitionMod
import Automata
import Minimiser

# Module: CFGraph

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SegNumPartition(p, m, maxSegNum, n):
        while True:
            with _dafny.label():
                if (n) <= (maxSegNum):
                    def lambda36_(d_659_m_, d_660_n_, d_661_p_):
                        def lambda37_(d_662_x_):
                            return (((d_659_m_)[d_662_x_]).seg) == (MiscTypes.Option_Some(d_660_n_))

                        return lambda37_

                    d_658_f_ = lambda36_(m, n, p)
                    d_663_p1_ = (p).SplitAt(d_658_f_, (len((p).elem)) - (1))
                    in94_ = d_663_p1_
                    in95_ = m
                    in96_ = maxSegNum
                    in97_ = (n) + (1)
                    p = in94_
                    m = in95_
                    maxSegNum = in96_
                    n = in97_
                    raise _dafny.TailCall()
                elif True:
                    return p
                break

    @staticmethod
    def EdgesToMap(edges, seenNodes, reverseSeenNodes, builtMap, lastNum, index):
        while True:
            with _dafny.label():
                if (len(edges)) == (index):
                    return (lastNum, builtMap, seenNodes, reverseSeenNodes)
                elif True:
                    let_tmp_rhs0_ = (((seenNodes)[((edges)[index]).src], lastNum, seenNodes, reverseSeenNodes) if (((edges)[index]).src) in ((seenNodes).keys) else ((lastNum) + (1), (lastNum) + (1), (seenNodes).set(((edges)[index]).src, (lastNum) + (1)), (reverseSeenNodes).set((lastNum) + (1), ((edges)[index]).src)))
                    d_664_src_ = let_tmp_rhs0_[0]
                    d_665_last_ = let_tmp_rhs0_[1]
                    d_666_m1_ = let_tmp_rhs0_[2]
                    d_667_rm1_ = let_tmp_rhs0_[3]
                    let_tmp_rhs1_ = (((d_666_m1_)[((edges)[index]).tgt], d_665_last_, d_666_m1_, d_667_rm1_) if (((edges)[index]).tgt) in ((d_666_m1_).keys) else ((d_665_last_) + (1), (d_665_last_) + (1), (d_666_m1_).set(((edges)[index]).tgt, (d_665_last_) + (1)), (d_667_rm1_).set((d_665_last_) + (1), ((edges)[index]).tgt)))
                    d_668_tgt_ = let_tmp_rhs1_[0]
                    d_669_last_k_ = let_tmp_rhs1_[1]
                    d_670_m2_ = let_tmp_rhs1_[2]
                    d_671_rm2_ = let_tmp_rhs1_[3]
                    d_672_b_ = (builtMap).set((d_664_src_, ((edges)[index]).lab), d_668_tgt_)
                    in98_ = edges
                    in99_ = d_670_m2_
                    in100_ = d_671_rm2_
                    in101_ = d_672_b_
                    in102_ = d_669_last_k_
                    in103_ = (index) + (1)
                    edges = in98_
                    seenNodes = in99_
                    reverseSeenNodes = in100_
                    builtMap = in101_
                    lastNum = in102_
                    index = in103_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def BoolsToString(x):
        d_673___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_673___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "E")))
                elif True:
                    d_673___accumulator_ = (d_673___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_dafny.CodePoint('1') if (x)[0] else _dafny.CodePoint('0'))]))
                    in104_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in104_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DOTSeg(xs, numSeg):
        d_674_s_ = (xs)[numSeg]
        d_675_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex((d_674_s_).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"CENTER\"/>\n")))
        d_676_body_ = default__.DOTIns((d_674_s_).Ins())
        return (d_675_prefix_) + (d_676_body_)

    @staticmethod
    def DOTIns(xi):
        d_677___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_677___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_678_a_ = (((xi)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))
                    d_677___accumulator_ = (d_677___accumulator_) + (d_678_a_)
                    in105_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in105_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def NatBoolEdgesToCFGEdges(xs, m, maxSegNum):
        d_679___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_679___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_679___accumulator_ = (d_679___accumulator_) + (_dafny.SeqWithoutIsStrInference([BoolEdge_BoolEdge((m)[((xs)[0])[0]], ((xs)[0])[1], (m)[((xs)[0])[2]])]))
                    in106_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in107_ = m
                    in108_ = maxSegNum
                    xs = in106_
                    m = in107_
                    maxSegNum = in108_
                    raise _dafny.TailCall()
                break


class CFGNode:
    @classmethod
    def default(cls, ):
        return lambda: CFGNode_CFGNode(_dafny.Seq({}), MiscTypes.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CFGNode(self) -> bool:
        return isinstance(self, CFGNode_CFGNode)
    def ToString(self):
        return default__.BoolsToString((self).id)


class CFGNode_CFGNode(CFGNode, NamedTuple('CFGNode', [('id', Any), ('seg', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.CFGNode.CFGNode({_dafny.string_of(self.id)}, {_dafny.string_of(self.seg)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CFGNode_CFGNode) and self.id == __o.id and self.seg == __o.seg
    def __hash__(self) -> int:
        return super().__hash__()


class BoolEdge:
    @classmethod
    def default(cls, ):
        return lambda: BoolEdge_BoolEdge(CFGNode.default()(), False, CFGNode.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_BoolEdge(self) -> bool:
        return isinstance(self, BoolEdge_BoolEdge)
    def DOTPrint(self):
        d_680_lab_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if (self).lab else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false")))
        return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [label=")))) + (d_680_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))


class BoolEdge_BoolEdge(BoolEdge, NamedTuple('BoolEdge', [('src', Any), ('lab', Any), ('tgt', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolEdge.BoolEdge({_dafny.string_of(self.src)}, {_dafny.string_of(self.lab)}, {_dafny.string_of(self.tgt)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolEdge_BoolEdge) and self.src == __o.src and self.lab == __o.lab and self.tgt == __o.tgt
    def __hash__(self) -> int:
        return super().__hash__()


class BoolCFGraph:
    @classmethod
    def default(cls, ):
        return lambda: BoolCFGraph_BoolCFGraph(_dafny.Seq({}), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_BoolCFGraph(self) -> bool:
        return isinstance(self, BoolCFGraph_BoolCFGraph)
    def AddEdge(self, e):
        return BoolCFGraph_BoolCFGraph((_dafny.SeqWithoutIsStrInference([e])) + ((self).edges), 0)

    def IsValid(self):
        def lambda38_(forall_var_10_):
            d_681_k_: int = forall_var_10_
            return not (((0) <= (d_681_k_)) and ((d_681_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_681_k_]).src).seg).is_Some) or (((((((self).edges)[d_681_k_]).src).seg).v) <= ((self).maxSegNum)))

        def lambda39_(forall_var_11_):
            d_682_k_: int = forall_var_11_
            return not (((0) <= (d_682_k_)) and ((d_682_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_682_k_]).tgt).seg).is_Some) or (((((((self).edges)[d_682_k_]).tgt).seg).v) <= ((self).maxSegNum)))

        return (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda38_)) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda39_))

    def Minimise(self):
        d_683_r_ = default__.EdgesToMap((self).edges, _dafny.Map({CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0)): 0}), _dafny.Map({0: CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}), _dafny.Map({}), 0, 0)
        d_684_idToNum_ = (d_683_r_)[2]
        d_685_numToCFGNode_ = (d_683_r_)[3]
        d_686_lastStateNum_ = (d_683_r_)[0]
        d_687_transitions_ = (d_683_r_)[1]
        d_688_a_ = Automata.Auto_Auto((d_686_lastStateNum_) + (1), d_687_transitions_)
        if (d_686_lastStateNum_) > (0):
            def iife16_():
                coll1_ = _dafny.Set()
                compr_1_: int
                for compr_1_ in _dafny.IntegerRange(0, (d_686_lastStateNum_) + (1)):
                    d_690_q_: int = compr_1_
                    if ((0) <= (d_690_q_)) and ((d_690_q_) < ((d_686_lastStateNum_) + (1))):
                        coll1_ = coll1_.union(_dafny.Set([d_690_q_]))
                return _dafny.Set(coll1_)
            d_689_s_ = iife16_()

            d_691_p_ = PartitionMod.Partition_Partition((d_686_lastStateNum_) + (1), _dafny.SeqWithoutIsStrInference([d_689_s_]))
            d_692_p1_ = default__.SegNumPartition(d_691_p_, d_685_numToCFGNode_, (self).maxSegNum, 0)
            d_693_vp_ = Minimiser.Pair_Pair(d_688_a_, d_692_p1_)
            d_694_minim_ = Minimiser.default__.Minimise(d_693_vp_)
            d_695_listOfEdges_ = (d_694_minim_).GenerateReduced(0)
            d_696_x_ = default__.NatBoolEdgesToCFGEdges(d_695_listOfEdges_, d_685_numToCFGNode_, (self).maxSegNum)
            d_697_miniCFG_ = BoolCFGraph_BoolCFGraph(d_696_x_, (self).maxSegNum)
            return d_697_miniCFG_
        elif True:
            return BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), (self).maxSegNum)

    def DOTPrintEdges(self, xe):
        d_698___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xe)) > (0):
                    d_698___accumulator_ = (d_698___accumulator_) + (((xe)[0]).DOTPrint())
                    in109_ = _this
                    in110_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    _this = in109_
                    
                    xe = in110_
                    raise _dafny.TailCall()
                elif True:
                    return (d_698___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodes(self, xs, g, printed):
        d_699___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                pat_let_tv2_ = xs
                pat_let_tv3_ = xs
                pat_let_tv4_ = g
                pat_let_tv5_ = xs
                pat_let_tv6_ = xs
                pat_let_tv7_ = g
                d_700_returnColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=olivedrab,fontcolor=white,"))
                d_701_revertColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=firebrick,fontcolor=white,"))
                d_702_branchColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
                if (len(g)) > (0):
                    def iife17_(_pat_let8_0):
                        def iife18_(d_704_numSeg_):
                            def iife19_(_pat_let9_0):
                                def iife20_(d_705_lab_):
                                    def lambda40_(source57_):
                                        if source57_.is_JUMPSeg:
                                            d_706___mcc_h0_ = source57_.ins
                                            d_707___mcc_h1_ = source57_.lastIns
                                            d_708___mcc_h2_ = source57_.netOpEffect
                                            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
                                        elif source57_.is_JUMPISeg:
                                            d_709___mcc_h6_ = source57_.ins
                                            d_710___mcc_h7_ = source57_.lastIns
                                            d_711___mcc_h8_ = source57_.netOpEffect
                                            return d_702_branchColour_
                                        elif source57_.is_RETURNSeg:
                                            d_712___mcc_h12_ = source57_.ins
                                            d_713___mcc_h13_ = source57_.lastIns
                                            d_714___mcc_h14_ = source57_.netOpEffect
                                            return d_700_returnColour_
                                        elif source57_.is_STOPSeg:
                                            d_715___mcc_h18_ = source57_.ins
                                            d_716___mcc_h19_ = source57_.lastIns
                                            d_717___mcc_h20_ = source57_.netOpEffect
                                            return d_701_revertColour_
                                        elif True:
                                            d_718___mcc_h24_ = source57_.ins
                                            d_719___mcc_h25_ = source57_.lastIns
                                            d_720___mcc_h26_ = source57_.netOpEffect
                                            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                                    def iife21_(_pat_let10_0):
                                        def iife22_(d_721_nodeColour_):
                                            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((pat_let_tv4_)[0]).src).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_721_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + (d_705_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))
                                        return iife22_(_pat_let10_0)
                                    return iife21_((lambda40_((pat_let_tv3_)[(d_704_numSeg_).v]) if (d_704_numSeg_).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))
                                return iife20_(_pat_let9_0)
                            return iife19_((default__.DOTSeg(pat_let_tv2_, (d_704_numSeg_).v) if (d_704_numSeg_).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorEnd <BR ALIGN=\"CENTER\"/>\n"))))
                        return iife18_(_pat_let8_0)
                    d_703_srctxt_ = (iife17_((((g)[0]).src).seg) if (((g)[0]).src) not in (printed) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    def iife23_(_pat_let11_0):
                        def iife24_(d_723_numSeg_):
                            def iife25_(_pat_let12_0):
                                def iife26_(d_724_lab_):
                                    def lambda41_(source58_):
                                        if source58_.is_JUMPSeg:
                                            d_725___mcc_h30_ = source58_.ins
                                            d_726___mcc_h31_ = source58_.lastIns
                                            d_727___mcc_h32_ = source58_.netOpEffect
                                            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
                                        elif source58_.is_JUMPISeg:
                                            d_728___mcc_h36_ = source58_.ins
                                            d_729___mcc_h37_ = source58_.lastIns
                                            d_730___mcc_h38_ = source58_.netOpEffect
                                            return d_702_branchColour_
                                        elif source58_.is_RETURNSeg:
                                            d_731___mcc_h42_ = source58_.ins
                                            d_732___mcc_h43_ = source58_.lastIns
                                            d_733___mcc_h44_ = source58_.netOpEffect
                                            return d_700_returnColour_
                                        elif source58_.is_STOPSeg:
                                            d_734___mcc_h48_ = source58_.ins
                                            d_735___mcc_h49_ = source58_.lastIns
                                            d_736___mcc_h50_ = source58_.netOpEffect
                                            return d_701_revertColour_
                                        elif True:
                                            d_737___mcc_h54_ = source58_.ins
                                            d_738___mcc_h55_ = source58_.lastIns
                                            d_739___mcc_h56_ = source58_.netOpEffect
                                            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

                                    def iife27_(_pat_let13_0):
                                        def iife28_(d_740_nodeColour_):
                                            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((pat_let_tv7_)[0]).tgt).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_740_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + (d_724_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))
                                        return iife28_(_pat_let13_0)
                                    return iife27_((lambda41_((pat_let_tv6_)[(d_723_numSeg_).v]) if (d_723_numSeg_).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))
                                return iife26_(_pat_let12_0)
                            return iife25_((default__.DOTSeg(pat_let_tv5_, (d_723_numSeg_).v) if (d_723_numSeg_).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorEnd <BR ALIGN=\"CENTER\"/>\n"))))
                        return iife24_(_pat_let11_0)
                    d_722_tgttxt_ = (iife23_((((g)[0]).tgt).seg) if ((((g)[0]).tgt) not in (printed)) and ((((g)[0]).src) != (((g)[0]).tgt)) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_699___accumulator_ = (d_699___accumulator_) + ((d_703_srctxt_) + (d_722_tgttxt_))
                    in111_ = _this
                    in112_ = xs
                    in113_ = _dafny.SeqWithoutIsStrInference((g)[1::])
                    in114_ = (printed) | (_dafny.Set({((g)[0]).src, ((g)[0]).tgt}))
                    _this = in111_
                    
                    xs = in112_
                    g = in113_
                    printed = in114_
                    raise _dafny.TailCall()
                elif True:
                    return (d_699___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrint(self, xs):
        d_741_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph CFG {\n node [shape=box]\nranking=TB\n "))
        return (((d_741_prefix_) + ((self).DOTPrintNodes(xs, (self).edges, _dafny.Set({})))) + ((self).DOTPrintEdges((self).edges))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n")))


class BoolCFGraph_BoolCFGraph(BoolCFGraph, NamedTuple('BoolCFGraph', [('edges', Any), ('maxSegNum', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolCFGraph.BoolCFGraph({_dafny.string_of(self.edges)}, {_dafny.string_of(self.maxSegNum)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolCFGraph_BoolCFGraph) and self.edges == __o.edges and self.maxSegNum == __o.maxSegNum
    def __hash__(self) -> int:
        return super().__hash__()

