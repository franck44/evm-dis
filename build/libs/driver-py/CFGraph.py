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
import PartitionMod
import Automata
import Minimiser

# Module: CFGraph

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BoolSeqToNat(xb):
        if (len(xb)) == (0):
            return 0
        elif True:
            return ((1 if (xb)[0] else 0)) + ((2) * (default__.BoolSeqToNat(_dafny.SeqWithoutIsStrInference((xb)[1::]))))

    @staticmethod
    def SegNumPartition(p, m, maxSegNum, n):
        while True:
            with _dafny.label():
                if (n) <= (maxSegNum):
                    def lambda51_(d_756_m_, d_757_n_, d_758_p_):
                        def lambda52_(d_759_x_):
                            return (((d_756_m_)[d_759_x_]).seg) == (MiscTypes.Option_Some(d_757_n_))

                        return lambda52_

                    d_755_f_ = lambda51_(m, n, p)
                    d_760_p1_ = (p).SplitAt(d_755_f_, (len((p).elem)) - (1))
                    in108_ = d_760_p1_
                    in109_ = m
                    in110_ = maxSegNum
                    in111_ = (n) + (1)
                    p = in108_
                    m = in109_
                    maxSegNum = in110_
                    n = in111_
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
                    d_761_src_ = let_tmp_rhs0_[0]
                    d_762_last_ = let_tmp_rhs0_[1]
                    d_763_m1_ = let_tmp_rhs0_[2]
                    d_764_rm1_ = let_tmp_rhs0_[3]
                    let_tmp_rhs1_ = (((d_763_m1_)[((edges)[index]).tgt], d_762_last_, d_763_m1_, d_764_rm1_) if (((edges)[index]).tgt) in ((d_763_m1_).keys) else ((d_762_last_) + (1), (d_762_last_) + (1), (d_763_m1_).set(((edges)[index]).tgt, (d_762_last_) + (1)), (d_764_rm1_).set((d_762_last_) + (1), ((edges)[index]).tgt)))
                    d_765_tgt_ = let_tmp_rhs1_[0]
                    d_766_last_k_ = let_tmp_rhs1_[1]
                    d_767_m2_ = let_tmp_rhs1_[2]
                    d_768_rm2_ = let_tmp_rhs1_[3]
                    d_769_b_ = (builtMap).set((d_761_src_, ((edges)[index]).lab), d_765_tgt_)
                    in112_ = edges
                    in113_ = d_767_m2_
                    in114_ = d_768_rm2_
                    in115_ = d_769_b_
                    in116_ = d_766_last_k_
                    in117_ = (index) + (1)
                    edges = in112_
                    seenNodes = in113_
                    reverseSeenNodes = in114_
                    builtMap = in115_
                    lastNum = in116_
                    index = in117_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def BoolsToString(x):
        d_770___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_770___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "E")))
                elif True:
                    d_770___accumulator_ = (d_770___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_dafny.CodePoint('1') if (x)[0] else _dafny.CodePoint('0'))]))
                    in118_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in118_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SegColour(s):
        source63_ = s
        if source63_.is_JUMPSeg:
            d_771___mcc_h0_ = source63_.ins
            d_772___mcc_h1_ = source63_.lastIns
            d_773___mcc_h2_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif source63_.is_JUMPISeg:
            d_774___mcc_h6_ = source63_.ins
            d_775___mcc_h7_ = source63_.lastIns
            d_776___mcc_h8_ = source63_.netOpEffect
            return default__.branchColour
        elif source63_.is_RETURNSeg:
            d_777___mcc_h12_ = source63_.ins
            d_778___mcc_h13_ = source63_.lastIns
            d_779___mcc_h14_ = source63_.netOpEffect
            return default__.returnColour
        elif source63_.is_STOPSeg:
            d_780___mcc_h18_ = source63_.ins
            d_781___mcc_h19_ = source63_.lastIns
            d_782___mcc_h20_ = source63_.netOpEffect
            return default__.revertColour
        elif source63_.is_CONTSeg:
            d_783___mcc_h24_ = source63_.ins
            d_784___mcc_h25_ = source63_.lastIns
            d_785___mcc_h26_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif True:
            d_786___mcc_h30_ = source63_.ins
            d_787___mcc_h31_ = source63_.lastIns
            d_788___mcc_h32_ = source63_.netOpEffect
            return default__.invalidColour

    @staticmethod
    def DOTSeg(s, numSeg):
        d_789_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</B><BR ALIGN=\"CENTER\"/>\n")))
        d_790_body_ = default__.DOTIns((s).Ins())
        return (d_789_prefix_) + (d_790_body_)

    @staticmethod
    def DOTIns(xi):
        d_791___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_791___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_792_a_ = (((xi)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))
                    d_791___accumulator_ = (d_791___accumulator_) + (d_792_a_)
                    in119_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in119_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def NatBoolEdgesToCFGEdges(xs, m, maxSegNum):
        d_793___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_793___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_793___accumulator_ = (d_793___accumulator_) + (_dafny.SeqWithoutIsStrInference([BoolEdge_BoolEdge((m)[((xs)[0])[0]], ((xs)[0])[1], (m)[((xs)[0])[2]])]))
                    in120_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in121_ = m
                    in122_ = maxSegNum
                    xs = in120_
                    m = in121_
                    maxSegNum = in122_
                    raise _dafny.TailCall()
                break

    @_dafny.classproperty
    def jcolour(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "royalblue"))
    @_dafny.classproperty
    def jumpColour(instance):
        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "color="))) + (default__.jcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ",")))
    @_dafny.classproperty
    def skcolour(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "black"))
    @_dafny.classproperty
    def skipColour(instance):
        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "color="))) + (default__.skcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ",")))
    @_dafny.classproperty
    def revertColour(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=orange,fontcolor=white,"))
    @_dafny.classproperty
    def returnColour(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=olivedrab,fontcolor=white,"))
    @_dafny.classproperty
    def invalidColour(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "style=filled,color=firebrick,fontcolor=white,"))
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

    def ToDot(self):
        d_794_x_ = default__.BoolSeqToNat((self).id)
        return ((Int.default__.NatToString(d_794_x_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "_")))) + (Int.default__.NatToString(len((self).id)))


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
    def DOTPrint2(self):
        d_795_lab1_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.jcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">jump</FONT>"))) if (self).lab else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.skcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">skip</FONT>"))))
        d_796_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_796_labColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<")))) + (d_795_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self):
        d_797_lab1_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Jump\",style=dashed")) if (self).lab else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Next\"")))
        d_798_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_797_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))


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
        def lambda53_(forall_var_10_):
            d_799_k_: int = forall_var_10_
            return not (((0) <= (d_799_k_)) and ((d_799_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_799_k_]).src).seg).is_Some) or (((((((self).edges)[d_799_k_]).src).seg).v) <= ((self).maxSegNum)))

        def lambda54_(forall_var_11_):
            d_800_k_: int = forall_var_11_
            return not (((0) <= (d_800_k_)) and ((d_800_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_800_k_]).tgt).seg).is_Some) or (((((((self).edges)[d_800_k_]).tgt).seg).v) <= ((self).maxSegNum)))

        return (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda53_)) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda54_))

    def Minimise(self):
        d_801_r_ = default__.EdgesToMap((self).edges, _dafny.Map({CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0)): 0}), _dafny.Map({0: CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}), _dafny.Map({}), 0, 0)
        d_802_idToNum_ = (d_801_r_)[2]
        d_803_numToCFGNode_ = (d_801_r_)[3]
        d_804_lastStateNum_ = (d_801_r_)[0]
        d_805_transitions_ = (d_801_r_)[1]
        d_806_a_ = Automata.Auto_Auto((d_804_lastStateNum_) + (1), d_805_transitions_)
        if (d_804_lastStateNum_) > (0):
            def iife16_():
                coll1_ = _dafny.Set()
                compr_1_: int
                for compr_1_ in _dafny.IntegerRange(0, (d_804_lastStateNum_) + (1)):
                    d_808_q_: int = compr_1_
                    if ((0) <= (d_808_q_)) and ((d_808_q_) < ((d_804_lastStateNum_) + (1))):
                        coll1_ = coll1_.union(_dafny.Set([d_808_q_]))
                return _dafny.Set(coll1_)
            d_807_s_ = iife16_()

            d_809_p_ = PartitionMod.Partition_Partition((d_804_lastStateNum_) + (1), _dafny.SeqWithoutIsStrInference([d_807_s_]))
            d_810_p1_ = default__.SegNumPartition(d_809_p_, d_803_numToCFGNode_, (self).maxSegNum, 0)
            d_811_vp_ = Minimiser.Pair_Pair(d_806_a_, d_810_p1_)
            d_812_minim_ = Minimiser.default__.Minimise(d_811_vp_)
            d_813_listOfEdges_ = (d_812_minim_).GenerateReduced(0)
            d_814_x_ = default__.NatBoolEdgesToCFGEdges(d_813_listOfEdges_, d_803_numToCFGNode_, (self).maxSegNum)
            d_815_miniCFG_ = BoolCFGraph_BoolCFGraph(d_814_x_, (self).maxSegNum)
            return d_815_miniCFG_
        elif True:
            return BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), (self).maxSegNum)

    def DOTPrintEdges(self, xe):
        d_816___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xe)) > (0):
                    d_816___accumulator_ = (d_816___accumulator_) + (((xe)[0]).DOTPrint())
                    in123_ = _this
                    in124_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    _this = in123_
                    
                    xe = in124_
                    raise _dafny.TailCall()
                elif True:
                    return (d_816___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodes(self, xs, g, printed):
        d_817___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(g)) > (0):
                    d_818_srctxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).src) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).src).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).src, (xs)[((((g)[0]).src).seg).v])))
                    d_819_tgttxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).tgt) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).tgt).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).tgt, (xs)[((((g)[0]).tgt).seg).v])))
                    d_817___accumulator_ = (d_817___accumulator_) + ((d_818_srctxt_) + (d_819_tgttxt_))
                    in125_ = _this
                    in126_ = xs
                    in127_ = _dafny.SeqWithoutIsStrInference((g)[1::])
                    in128_ = (printed) | (_dafny.Set({((g)[0]).src, ((g)[0]).tgt}))
                    _this = in125_
                    
                    xs = in126_
                    g = in127_
                    printed = in128_
                    raise _dafny.TailCall()
                elif True:
                    return (d_817___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodeLabel(self, n, s):
        d_820_lab_ = default__.DOTSeg(s, ((n).seg).v)
        d_821_nodeColour_ = default__.SegColour(s)
        return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_821_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + (d_820_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, xs):
        d_822_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph CFG {\n node [shape=box]\nnode[fontname=arial]\nedge[fontname=arial]\nranking=TB\n "))
        return (((d_822_prefix_) + ((self).DOTPrintNodes(xs, (self).edges, _dafny.Set({})))) + ((self).DOTPrintEdges((self).edges))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n")))


class BoolCFGraph_BoolCFGraph(BoolCFGraph, NamedTuple('BoolCFGraph', [('edges', Any), ('maxSegNum', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolCFGraph.BoolCFGraph({_dafny.string_of(self.edges)}, {_dafny.string_of(self.maxSegNum)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolCFGraph_BoolCFGraph) and self.edges == __o.edges and self.maxSegNum == __o.maxSegNum
    def __hash__(self) -> int:
        return super().__hash__()

