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
                    def lambda36_(d_701_m_, d_702_n_, d_703_p_):
                        def lambda37_(d_704_x_):
                            return (((d_701_m_)[d_704_x_]).seg) == (MiscTypes.Option_Some(d_702_n_))

                        return lambda37_

                    d_700_f_ = lambda36_(m, n, p)
                    d_705_p1_ = (p).SplitAt(d_700_f_, (len((p).elem)) - (1))
                    in102_ = d_705_p1_
                    in103_ = m
                    in104_ = maxSegNum
                    in105_ = (n) + (1)
                    p = in102_
                    m = in103_
                    maxSegNum = in104_
                    n = in105_
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
                    d_706_src_ = let_tmp_rhs0_[0]
                    d_707_last_ = let_tmp_rhs0_[1]
                    d_708_m1_ = let_tmp_rhs0_[2]
                    d_709_rm1_ = let_tmp_rhs0_[3]
                    let_tmp_rhs1_ = (((d_708_m1_)[((edges)[index]).tgt], d_707_last_, d_708_m1_, d_709_rm1_) if (((edges)[index]).tgt) in ((d_708_m1_).keys) else ((d_707_last_) + (1), (d_707_last_) + (1), (d_708_m1_).set(((edges)[index]).tgt, (d_707_last_) + (1)), (d_709_rm1_).set((d_707_last_) + (1), ((edges)[index]).tgt)))
                    d_710_tgt_ = let_tmp_rhs1_[0]
                    d_711_last_k_ = let_tmp_rhs1_[1]
                    d_712_m2_ = let_tmp_rhs1_[2]
                    d_713_rm2_ = let_tmp_rhs1_[3]
                    d_714_b_ = (builtMap).set((d_706_src_, ((edges)[index]).lab), d_710_tgt_)
                    in106_ = edges
                    in107_ = d_712_m2_
                    in108_ = d_713_rm2_
                    in109_ = d_714_b_
                    in110_ = d_711_last_k_
                    in111_ = (index) + (1)
                    edges = in106_
                    seenNodes = in107_
                    reverseSeenNodes = in108_
                    builtMap = in109_
                    lastNum = in110_
                    index = in111_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def BoolsToString(x):
        d_715___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_715___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "E")))
                elif True:
                    d_715___accumulator_ = (d_715___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_dafny.CodePoint('1') if (x)[0] else _dafny.CodePoint('0'))]))
                    in112_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in112_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DOTSeg(xs, numSeg):
        d_716_s_ = (xs)[numSeg]
        d_717_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex((d_716_s_).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"CENTER\"/>\n")))
        d_718_body_ = default__.DOTIns((d_716_s_).Ins())
        return (d_717_prefix_) + (d_718_body_)

    @staticmethod
    def SegColour(s):
        source63_ = s
        if source63_.is_JUMPSeg:
            d_719___mcc_h0_ = source63_.ins
            d_720___mcc_h1_ = source63_.lastIns
            d_721___mcc_h2_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif source63_.is_JUMPISeg:
            d_722___mcc_h6_ = source63_.ins
            d_723___mcc_h7_ = source63_.lastIns
            d_724___mcc_h8_ = source63_.netOpEffect
            return default__.branchColour
        elif source63_.is_RETURNSeg:
            d_725___mcc_h12_ = source63_.ins
            d_726___mcc_h13_ = source63_.lastIns
            d_727___mcc_h14_ = source63_.netOpEffect
            return default__.returnColour
        elif source63_.is_STOPSeg:
            d_728___mcc_h18_ = source63_.ins
            d_729___mcc_h19_ = source63_.lastIns
            d_730___mcc_h20_ = source63_.netOpEffect
            return default__.revertColour
        elif source63_.is_CONTSeg:
            d_731___mcc_h24_ = source63_.ins
            d_732___mcc_h25_ = source63_.lastIns
            d_733___mcc_h26_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif True:
            d_734___mcc_h30_ = source63_.ins
            d_735___mcc_h31_ = source63_.lastIns
            d_736___mcc_h32_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

    @staticmethod
    def DOTSeg2(s, numSeg):
        d_737_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<BR ALIGN=\"CENTER\"/>\n")))
        d_738_body_ = default__.DOTIns((s).Ins())
        return (d_737_prefix_) + (d_738_body_)

    @staticmethod
    def DOTIns(xi):
        d_739___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_739___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_740_a_ = (((xi)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))
                    d_739___accumulator_ = (d_739___accumulator_) + (d_740_a_)
                    in113_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in113_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def NatBoolEdgesToCFGEdges(xs, m, maxSegNum):
        d_741___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_741___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_741___accumulator_ = (d_741___accumulator_) + (_dafny.SeqWithoutIsStrInference([BoolEdge_BoolEdge((m)[((xs)[0])[0]], ((xs)[0])[1], (m)[((xs)[0])[2]])]))
                    in114_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in115_ = m
                    in116_ = maxSegNum
                    xs = in114_
                    m = in115_
                    maxSegNum = in116_
                    raise _dafny.TailCall()
                break

    @_dafny.classproperty
    def revertColour(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=firebrick,fontcolor=white,"))
    @_dafny.classproperty
    def returnColour(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=olivedrab,fontcolor=white,"))
    @_dafny.classproperty
    def branchColour(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))

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
        d_742_lab_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true")) if (self).lab else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false")))
        return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [label=")))) + (d_742_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))


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
            d_743_k_: int = forall_var_10_
            return not (((0) <= (d_743_k_)) and ((d_743_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_743_k_]).src).seg).is_Some) or (((((((self).edges)[d_743_k_]).src).seg).v) <= ((self).maxSegNum)))

        def lambda39_(forall_var_11_):
            d_744_k_: int = forall_var_11_
            return not (((0) <= (d_744_k_)) and ((d_744_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_744_k_]).tgt).seg).is_Some) or (((((((self).edges)[d_744_k_]).tgt).seg).v) <= ((self).maxSegNum)))

        return (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda38_)) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda39_))

    def Minimise(self):
        d_745_r_ = default__.EdgesToMap((self).edges, _dafny.Map({CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0)): 0}), _dafny.Map({0: CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}), _dafny.Map({}), 0, 0)
        d_746_idToNum_ = (d_745_r_)[2]
        d_747_numToCFGNode_ = (d_745_r_)[3]
        d_748_lastStateNum_ = (d_745_r_)[0]
        d_749_transitions_ = (d_745_r_)[1]
        d_750_a_ = Automata.Auto_Auto((d_748_lastStateNum_) + (1), d_749_transitions_)
        if (d_748_lastStateNum_) > (0):
            def iife16_():
                coll1_ = _dafny.Set()
                compr_1_: int
                for compr_1_ in _dafny.IntegerRange(0, (d_748_lastStateNum_) + (1)):
                    d_752_q_: int = compr_1_
                    if ((0) <= (d_752_q_)) and ((d_752_q_) < ((d_748_lastStateNum_) + (1))):
                        coll1_ = coll1_.union(_dafny.Set([d_752_q_]))
                return _dafny.Set(coll1_)
            d_751_s_ = iife16_()

            d_753_p_ = PartitionMod.Partition_Partition((d_748_lastStateNum_) + (1), _dafny.SeqWithoutIsStrInference([d_751_s_]))
            d_754_p1_ = default__.SegNumPartition(d_753_p_, d_747_numToCFGNode_, (self).maxSegNum, 0)
            d_755_vp_ = Minimiser.Pair_Pair(d_750_a_, d_754_p1_)
            d_756_minim_ = Minimiser.default__.Minimise(d_755_vp_)
            d_757_listOfEdges_ = (d_756_minim_).GenerateReduced(0)
            d_758_x_ = default__.NatBoolEdgesToCFGEdges(d_757_listOfEdges_, d_747_numToCFGNode_, (self).maxSegNum)
            d_759_miniCFG_ = BoolCFGraph_BoolCFGraph(d_758_x_, (self).maxSegNum)
            return d_759_miniCFG_
        elif True:
            return BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), (self).maxSegNum)

    def DOTPrintEdges(self, xe):
        d_760___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xe)) > (0):
                    d_760___accumulator_ = (d_760___accumulator_) + (((xe)[0]).DOTPrint())
                    in117_ = _this
                    in118_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    _this = in117_
                    
                    xe = in118_
                    raise _dafny.TailCall()
                elif True:
                    return (d_760___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodes(self, xs, g, printed):
        d_761___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                d_762_returnColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=olivedrab,fontcolor=white,"))
                d_763_revertColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=firebrick,fontcolor=white,"))
                d_764_branchColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
                if (len(g)) > (0):
                    d_765_srctxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).src) in (printed) else (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorEnd <BR ALIGN=\"CENTER\"/>\n")) if ((((g)[0]).src).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).src, (xs)[((((g)[0]).src).seg).v])))
                    d_766_tgttxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).tgt) in (printed) else (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorEnd <BR ALIGN=\"CENTER\"/>\n")) if ((((g)[0]).tgt).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).tgt, (xs)[((((g)[0]).tgt).seg).v])))
                    d_761___accumulator_ = (d_761___accumulator_) + ((d_765_srctxt_) + (d_766_tgttxt_))
                    in119_ = _this
                    in120_ = xs
                    in121_ = _dafny.SeqWithoutIsStrInference((g)[1::])
                    in122_ = (printed) | (_dafny.Set({((g)[0]).src, ((g)[0]).tgt}))
                    _this = in119_
                    
                    xs = in120_
                    g = in121_
                    printed = in122_
                    raise _dafny.TailCall()
                elif True:
                    return (d_761___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodeLabel(self, n, s):
        d_767_lab_ = (default__.DOTSeg2(s, ((n).seg).v) if ((n).seg).is_Some else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorEnd <BR ALIGN=\"CENTER\"/>\n")))
        d_768_nodeColour_ = default__.SegColour(s)
        return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_768_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + (default__.DOTSeg2(s, ((n).seg).v))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, xs):
        d_769_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph CFG {\n node [shape=box]\nranking=TB\n "))
        return (((d_769_prefix_) + ((self).DOTPrintNodes(xs, (self).edges, _dafny.Set({})))) + ((self).DOTPrintEdges((self).edges))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n")))


class BoolCFGraph_BoolCFGraph(BoolCFGraph, NamedTuple('BoolCFGraph', [('edges', Any), ('maxSegNum', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolCFGraph.BoolCFGraph({_dafny.string_of(self.edges)}, {_dafny.string_of(self.maxSegNum)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolCFGraph_BoolCFGraph) and self.edges == __o.edges and self.maxSegNum == __o.maxSegNum
    def __hash__(self) -> int:
        return super().__hash__()

