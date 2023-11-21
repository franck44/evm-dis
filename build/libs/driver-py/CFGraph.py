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
    def SegNumPartition(p, m, maxSegNum, n):
        while True:
            with _dafny.label():
                if (n) <= (maxSegNum):
                    def lambda36_(d_712_m_, d_713_n_, d_714_p_):
                        def lambda37_(d_715_x_):
                            return (((d_712_m_)[d_715_x_]).seg) == (MiscTypes.Option_Some(d_713_n_))

                        return lambda37_

                    d_711_f_ = lambda36_(m, n, p)
                    d_716_p1_ = (p).SplitAt(d_711_f_, (len((p).elem)) - (1))
                    in108_ = d_716_p1_
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
                    d_717_src_ = let_tmp_rhs0_[0]
                    d_718_last_ = let_tmp_rhs0_[1]
                    d_719_m1_ = let_tmp_rhs0_[2]
                    d_720_rm1_ = let_tmp_rhs0_[3]
                    let_tmp_rhs1_ = (((d_719_m1_)[((edges)[index]).tgt], d_718_last_, d_719_m1_, d_720_rm1_) if (((edges)[index]).tgt) in ((d_719_m1_).keys) else ((d_718_last_) + (1), (d_718_last_) + (1), (d_719_m1_).set(((edges)[index]).tgt, (d_718_last_) + (1)), (d_720_rm1_).set((d_718_last_) + (1), ((edges)[index]).tgt)))
                    d_721_tgt_ = let_tmp_rhs1_[0]
                    d_722_last_k_ = let_tmp_rhs1_[1]
                    d_723_m2_ = let_tmp_rhs1_[2]
                    d_724_rm2_ = let_tmp_rhs1_[3]
                    d_725_b_ = (builtMap).set((d_717_src_, ((edges)[index]).lab), d_721_tgt_)
                    in112_ = edges
                    in113_ = d_723_m2_
                    in114_ = d_724_rm2_
                    in115_ = d_725_b_
                    in116_ = d_722_last_k_
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
        d_726___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_726___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "E")))
                elif True:
                    d_726___accumulator_ = (d_726___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_dafny.CodePoint('1') if (x)[0] else _dafny.CodePoint('0'))]))
                    in118_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in118_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DOTSeg(xs, numSeg):
        d_727_s_ = (xs)[numSeg]
        d_728_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex((d_727_s_).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</B><BR ALIGN=\"CENTER\"/>\n")))
        d_729_body_ = default__.DOTIns((d_727_s_).Ins())
        return (d_728_prefix_) + (d_729_body_)

    @staticmethod
    def SegColour(s):
        source63_ = s
        if source63_.is_JUMPSeg:
            d_730___mcc_h0_ = source63_.ins
            d_731___mcc_h1_ = source63_.lastIns
            d_732___mcc_h2_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif source63_.is_JUMPISeg:
            d_733___mcc_h6_ = source63_.ins
            d_734___mcc_h7_ = source63_.lastIns
            d_735___mcc_h8_ = source63_.netOpEffect
            return default__.branchColour
        elif source63_.is_RETURNSeg:
            d_736___mcc_h12_ = source63_.ins
            d_737___mcc_h13_ = source63_.lastIns
            d_738___mcc_h14_ = source63_.netOpEffect
            return default__.returnColour
        elif source63_.is_STOPSeg:
            d_739___mcc_h18_ = source63_.ins
            d_740___mcc_h19_ = source63_.lastIns
            d_741___mcc_h20_ = source63_.netOpEffect
            return default__.revertColour
        elif source63_.is_CONTSeg:
            d_742___mcc_h24_ = source63_.ins
            d_743___mcc_h25_ = source63_.lastIns
            d_744___mcc_h26_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif True:
            d_745___mcc_h30_ = source63_.ins
            d_746___mcc_h31_ = source63_.lastIns
            d_747___mcc_h32_ = source63_.netOpEffect
            return default__.invalidColour

    @staticmethod
    def DOTSeg2(s, numSeg):
        d_748_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</B><BR ALIGN=\"CENTER\"/>\n")))
        d_749_body_ = default__.DOTIns((s).Ins())
        return (d_748_prefix_) + (d_749_body_)

    @staticmethod
    def DOTIns(xi):
        d_750___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_750___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_751_a_ = (((xi)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))
                    d_750___accumulator_ = (d_750___accumulator_) + (d_751_a_)
                    in119_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in119_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def NatBoolEdgesToCFGEdges(xs, m, maxSegNum):
        d_752___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_752___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_752___accumulator_ = (d_752___accumulator_) + (_dafny.SeqWithoutIsStrInference([BoolEdge_BoolEdge((m)[((xs)[0])[0]], ((xs)[0])[1], (m)[((xs)[0])[2]])]))
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
        d_753_lab1_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.jcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">jump</FONT>"))) if (self).lab else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.skcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">skip</FONT>"))))
        d_754_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_754_labColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<")))) + (d_753_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))


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
            d_755_k_: int = forall_var_10_
            return not (((0) <= (d_755_k_)) and ((d_755_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_755_k_]).src).seg).is_Some) or (((((((self).edges)[d_755_k_]).src).seg).v) <= ((self).maxSegNum)))

        def lambda39_(forall_var_11_):
            d_756_k_: int = forall_var_11_
            return not (((0) <= (d_756_k_)) and ((d_756_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_756_k_]).tgt).seg).is_Some) or (((((((self).edges)[d_756_k_]).tgt).seg).v) <= ((self).maxSegNum)))

        return (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda38_)) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda39_))

    def Minimise(self):
        d_757_r_ = default__.EdgesToMap((self).edges, _dafny.Map({CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0)): 0}), _dafny.Map({0: CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}), _dafny.Map({}), 0, 0)
        d_758_idToNum_ = (d_757_r_)[2]
        d_759_numToCFGNode_ = (d_757_r_)[3]
        d_760_lastStateNum_ = (d_757_r_)[0]
        d_761_transitions_ = (d_757_r_)[1]
        d_762_a_ = Automata.Auto_Auto((d_760_lastStateNum_) + (1), d_761_transitions_)
        if (d_760_lastStateNum_) > (0):
            def iife16_():
                coll1_ = _dafny.Set()
                compr_1_: int
                for compr_1_ in _dafny.IntegerRange(0, (d_760_lastStateNum_) + (1)):
                    d_764_q_: int = compr_1_
                    if ((0) <= (d_764_q_)) and ((d_764_q_) < ((d_760_lastStateNum_) + (1))):
                        coll1_ = coll1_.union(_dafny.Set([d_764_q_]))
                return _dafny.Set(coll1_)
            d_763_s_ = iife16_()

            d_765_p_ = PartitionMod.Partition_Partition((d_760_lastStateNum_) + (1), _dafny.SeqWithoutIsStrInference([d_763_s_]))
            d_766_p1_ = default__.SegNumPartition(d_765_p_, d_759_numToCFGNode_, (self).maxSegNum, 0)
            d_767_vp_ = Minimiser.Pair_Pair(d_762_a_, d_766_p1_)
            d_768_minim_ = Minimiser.default__.Minimise(d_767_vp_)
            d_769_listOfEdges_ = (d_768_minim_).GenerateReduced(0)
            d_770_x_ = default__.NatBoolEdgesToCFGEdges(d_769_listOfEdges_, d_759_numToCFGNode_, (self).maxSegNum)
            d_771_miniCFG_ = BoolCFGraph_BoolCFGraph(d_770_x_, (self).maxSegNum)
            return d_771_miniCFG_
        elif True:
            return BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), (self).maxSegNum)

    def DOTPrintEdges(self, xe):
        d_772___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xe)) > (0):
                    d_772___accumulator_ = (d_772___accumulator_) + (((xe)[0]).DOTPrint())
                    in123_ = _this
                    in124_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    _this = in123_
                    
                    xe = in124_
                    raise _dafny.TailCall()
                elif True:
                    return (d_772___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodes(self, xs, g, printed):
        d_773___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(g)) > (0):
                    d_774_srctxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).src) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).src).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).src).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).src, (xs)[((((g)[0]).src).seg).v])))
                    d_775_tgttxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).tgt) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).tgt).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).tgt).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).tgt, (xs)[((((g)[0]).tgt).seg).v])))
                    d_773___accumulator_ = (d_773___accumulator_) + ((d_774_srctxt_) + (d_775_tgttxt_))
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
                    return (d_773___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodeLabel(self, n, s):
        d_776_lab_ = default__.DOTSeg2(s, ((n).seg).v)
        d_777_nodeColour_ = default__.SegColour(s)
        return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_777_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + (d_776_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, xs):
        d_778_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph CFG {\n node [shape=box]\nnode[fontname=arial]\nedge[fontname=arial]\nranking=TB\n "))
        return (((d_778_prefix_) + ((self).DOTPrintNodes(xs, (self).edges, _dafny.Set({})))) + ((self).DOTPrintEdges((self).edges))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n")))


class BoolCFGraph_BoolCFGraph(BoolCFGraph, NamedTuple('BoolCFGraph', [('edges', Any), ('maxSegNum', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolCFGraph.BoolCFGraph({_dafny.string_of(self.edges)}, {_dafny.string_of(self.maxSegNum)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolCFGraph_BoolCFGraph) and self.edges == __o.edges and self.maxSegNum == __o.maxSegNum
    def __hash__(self) -> int:
        return super().__hash__()

