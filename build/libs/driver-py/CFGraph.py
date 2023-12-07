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
                    def lambda51_(d_860_m_, d_861_n_, d_862_p_):
                        def lambda52_(d_863_x_):
                            return (((d_860_m_)[d_863_x_]).seg) == (MiscTypes.Option_Some(d_861_n_))

                        return lambda52_

                    d_859_f_ = lambda51_(m, n, p)
                    d_864_p1_ = (p).SplitAt(d_859_f_, (len((p).elem)) - (1))
                    in109_ = d_864_p1_
                    in110_ = m
                    in111_ = maxSegNum
                    in112_ = (n) + (1)
                    p = in109_
                    m = in110_
                    maxSegNum = in111_
                    n = in112_
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
                    d_865_src_ = let_tmp_rhs0_[0]
                    d_866_last_ = let_tmp_rhs0_[1]
                    d_867_m1_ = let_tmp_rhs0_[2]
                    d_868_rm1_ = let_tmp_rhs0_[3]
                    let_tmp_rhs1_ = (((d_867_m1_)[((edges)[index]).tgt], d_866_last_, d_867_m1_, d_868_rm1_) if (((edges)[index]).tgt) in ((d_867_m1_).keys) else ((d_866_last_) + (1), (d_866_last_) + (1), (d_867_m1_).set(((edges)[index]).tgt, (d_866_last_) + (1)), (d_868_rm1_).set((d_866_last_) + (1), ((edges)[index]).tgt)))
                    d_869_tgt_ = let_tmp_rhs1_[0]
                    d_870_last_k_ = let_tmp_rhs1_[1]
                    d_871_m2_ = let_tmp_rhs1_[2]
                    d_872_rm2_ = let_tmp_rhs1_[3]
                    d_873_b_ = (builtMap).set((d_865_src_, ((edges)[index]).lab), d_869_tgt_)
                    in113_ = edges
                    in114_ = d_871_m2_
                    in115_ = d_872_rm2_
                    in116_ = d_873_b_
                    in117_ = d_870_last_k_
                    in118_ = (index) + (1)
                    edges = in113_
                    seenNodes = in114_
                    reverseSeenNodes = in115_
                    builtMap = in116_
                    lastNum = in117_
                    index = in118_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def BoolsToString(x):
        d_874___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_874___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "E")))
                elif True:
                    d_874___accumulator_ = (d_874___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_dafny.CodePoint('1') if (x)[0] else _dafny.CodePoint('0'))]))
                    in119_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in119_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SegColour(s):
        source63_ = s
        if source63_.is_JUMPSeg:
            d_875___mcc_h0_ = source63_.ins
            d_876___mcc_h1_ = source63_.lastIns
            d_877___mcc_h2_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif source63_.is_JUMPISeg:
            d_878___mcc_h6_ = source63_.ins
            d_879___mcc_h7_ = source63_.lastIns
            d_880___mcc_h8_ = source63_.netOpEffect
            return default__.branchColour
        elif source63_.is_RETURNSeg:
            d_881___mcc_h12_ = source63_.ins
            d_882___mcc_h13_ = source63_.lastIns
            d_883___mcc_h14_ = source63_.netOpEffect
            return default__.returnColour
        elif source63_.is_STOPSeg:
            d_884___mcc_h18_ = source63_.ins
            d_885___mcc_h19_ = source63_.lastIns
            d_886___mcc_h20_ = source63_.netOpEffect
            return default__.revertColour
        elif source63_.is_CONTSeg:
            d_887___mcc_h24_ = source63_.ins
            d_888___mcc_h25_ = source63_.lastIns
            d_889___mcc_h26_ = source63_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif True:
            d_890___mcc_h30_ = source63_.ins
            d_891___mcc_h31_ = source63_.lastIns
            d_892___mcc_h32_ = source63_.netOpEffect
            return default__.invalidColour

    @staticmethod
    def DOTSeg(s, numSeg):
        def iife16_(_pat_let8_0):
            def iife17_(d_894_r_):
                def lambda53_(source64_):
                    if source64_.is_Left:
                        d_895___mcc_h0_ = source64_.l
                        def iife18_(_pat_let9_0):
                            def iife19_(d_896_v_):
                                def lambda54_(source65_):
                                    if source65_.is_Value:
                                        d_897___mcc_h2_ = source65_.v
                                        def iife20_(_pat_let10_0):
                                            def iife21_(d_898_address_):
                                                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Constant 0x"))) + (Hex.default__.NatToHex(d_898_address_))
                                            return iife21_(_pat_let10_0)
                                        return iife20_(d_897___mcc_h2_)
                                    elif True:
                                        d_899___mcc_h3_ = source65_.s
                                        def iife22_(_pat_let11_0):
                                            def iife23_(d_900_msg_):
                                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Unknown"))
                                            return iife23_(_pat_let11_0)
                                        return iife22_(d_899___mcc_h3_)

                                return lambda54_(d_896_v_)
                            return iife19_(_pat_let9_0)
                        return iife18_(d_895___mcc_h0_)
                    elif True:
                        d_901___mcc_h1_ = source64_.r
                        def iife24_(_pat_let12_0):
                            def iife25_(d_902_stackPos_):
                                return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Stack on Entry.Peek("))) + (Int.default__.NatToString(d_902_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
                            return iife25_(_pat_let12_0)
                        return iife24_(d_901___mcc_h1_)

                return lambda53_(d_894_r_)
            return iife17_(_pat_let8_0)
        d_893_jumpTip_ = (iife16_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_903_stackSizeEffect_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size &#916;: "))) + (Int.default__.IntToString((s).StackEffect()))
        d_904_mninNumOpe_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Stack Size on Entry &#8805; "))) + (Int.default__.NatToString((s).WeakestPreOperands(0)))
        d_905_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</B><BR ALIGN=\"CENTER\"/>\n")))
        d_906_body_ = default__.DOTIns((s).Ins())
        return ((d_905_prefix_) + (d_906_body_), ((d_903_stackSizeEffect_) + (d_893_jumpTip_)) + (d_904_mninNumOpe_))

    @staticmethod
    def DOTSegTable(s, numSeg):
        def iife26_(_pat_let13_0):
            def iife27_(d_908_r_):
                def lambda55_(source66_):
                    if source66_.is_Left:
                        d_909___mcc_h0_ = source66_.l
                        def iife28_(_pat_let14_0):
                            def iife29_(d_910_v_):
                                def lambda56_(source67_):
                                    if source67_.is_Value:
                                        d_911___mcc_h2_ = source67_.v
                                        def iife30_(_pat_let15_0):
                                            def iife31_(d_912_address_):
                                                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Constant 0x"))) + (Hex.default__.NatToHex(d_912_address_))
                                            return iife31_(_pat_let15_0)
                                        return iife30_(d_911___mcc_h2_)
                                    elif True:
                                        d_913___mcc_h3_ = source67_.s
                                        def iife32_(_pat_let16_0):
                                            def iife33_(d_914_msg_):
                                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Unknown"))
                                            return iife33_(_pat_let16_0)
                                        return iife32_(d_913___mcc_h3_)

                                return lambda56_(d_910_v_)
                            return iife29_(_pat_let14_0)
                        return iife28_(d_909___mcc_h0_)
                    elif True:
                        d_915___mcc_h1_ = source66_.r
                        def iife34_(_pat_let17_0):
                            def iife35_(d_916_stackPos_):
                                return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Stack on Entry.Peek("))) + (Int.default__.NatToString(d_916_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
                            return iife35_(_pat_let17_0)
                        return iife34_(d_915___mcc_h1_)

                return lambda55_(d_908_r_)
            return iife27_(_pat_let13_0)
        d_907_jumpTip_ = (iife26_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_917_tableStart_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE ALIGN=\"LEFT\" CELLBORDER=\"0\" BORDER=\"0\" cellpadding=\"0\"  CELLSPACING=\"1\">\n"))
        d_918_prefix_ = ((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">Segment ")))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"\" tooltip=\"Stack Size &#916;: ")))) + (Int.default__.IntToString((s).StackEffect()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Stack Size on Entry &#8805; ")))) + (Int.default__.NatToString((s).WeakestPreOperands(0)))) + (d_907_jumpTip_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "><FONT color=\"green\">&#9636;</FONT></TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR><HR/>\n")))
        d_919_tableEnd_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>\n"))
        d_920_body_ = default__.DOTInsTable((s).Ins(), True)
        return (((d_917_tableStart_) + (d_918_prefix_)) + (d_920_body_)) + (d_919_tableEnd_)

    @staticmethod
    def DOTIns(xi):
        d_921___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_921___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_921___accumulator_ = (d_921___accumulator_) + (((xi)[0]).ToHTML())
                    in120_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in120_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DOTInsTable(xi, isFirst):
        d_922___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_922___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_923_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n"))
                    d_924_suffix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD></TR>\n"))
                    d_925_exitPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"exit\"")) if ((xi)[0]).IsJump() else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_926_entryPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"entry\"")) if isFirst else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_927_a_ = ((xi)[0]).ToHTMLTable(d_926_entryPortTag_, d_925_exitPortTag_)
                    d_922___accumulator_ = (d_922___accumulator_) + (((d_923_prefix_) + (d_927_a_)) + (d_924_suffix_))
                    in121_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    in122_ = False
                    xi = in121_
                    isFirst = in122_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def NatBoolEdgesToCFGEdges(xs, m, maxSegNum):
        d_928___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_928___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_928___accumulator_ = (d_928___accumulator_) + (_dafny.SeqWithoutIsStrInference([BoolEdge_BoolEdge((m)[((xs)[0])[0]], ((xs)[0])[1], (m)[((xs)[0])[2]])]))
                    in123_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in124_ = m
                    in125_ = maxSegNum
                    xs = in123_
                    m = in124_
                    maxSegNum = in125_
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
        d_929_x_ = default__.BoolSeqToNat((self).id)
        return ((Int.default__.NatToString(d_929_x_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "_")))) + (Int.default__.NatToString(len((self).id)))


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
        d_930_lab1_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.jcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">jump</FONT>"))) if (self).lab else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.skcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">skip</FONT>"))))
        d_931_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_931_labColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<")))) + (d_930_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, fancyExit):
        d_932_lab1_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Jump\",style=dashed")) if (self).lab else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Next\"")))
        d_933_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        d_934_exitPort_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":exit:se ")) if (fancyExit) and ((self).lab) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_935_entryPort_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":entry:w ")) if (fancyExit) and ((self).lab) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToDot())) + (d_934_exitPort_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToDot())) + (d_935_entryPort_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_932_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))


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

    def numNodes(self):
        return 0

    def numEdges(self):
        return len((self).edges)

    def IsValid(self):
        def lambda57_(forall_var_10_):
            d_936_k_: int = forall_var_10_
            return not (((0) <= (d_936_k_)) and ((d_936_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_936_k_]).src).seg).is_Some) or (((((((self).edges)[d_936_k_]).src).seg).v) <= ((self).maxSegNum)))

        def lambda58_(forall_var_11_):
            d_937_k_: int = forall_var_11_
            return not (((0) <= (d_937_k_)) and ((d_937_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_937_k_]).tgt).seg).is_Some) or (((((((self).edges)[d_937_k_]).tgt).seg).v) <= ((self).maxSegNum)))

        return (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda57_)) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda58_))

    def Minimise(self):
        d_938_r_ = default__.EdgesToMap((self).edges, _dafny.Map({CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0)): 0}), _dafny.Map({0: CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}), _dafny.Map({}), 0, 0)
        d_939_idToNum_ = (d_938_r_)[2]
        d_940_numToCFGNode_ = (d_938_r_)[3]
        d_941_lastStateNum_ = (d_938_r_)[0]
        d_942_transitions_ = (d_938_r_)[1]
        d_943_a_ = Automata.Auto_Auto((d_941_lastStateNum_) + (1), d_942_transitions_)
        if (d_941_lastStateNum_) > (0):
            def iife36_():
                coll1_ = _dafny.Set()
                compr_1_: int
                for compr_1_ in _dafny.IntegerRange(0, (d_941_lastStateNum_) + (1)):
                    d_945_q_: int = compr_1_
                    if ((0) <= (d_945_q_)) and ((d_945_q_) < ((d_941_lastStateNum_) + (1))):
                        coll1_ = coll1_.union(_dafny.Set([d_945_q_]))
                return _dafny.Set(coll1_)
            d_944_s_ = iife36_()

            d_946_p_ = PartitionMod.Partition_Partition((d_941_lastStateNum_) + (1), _dafny.SeqWithoutIsStrInference([d_944_s_]))
            d_947_p1_ = default__.SegNumPartition(d_946_p_, d_940_numToCFGNode_, (self).maxSegNum, 0)
            d_948_vp_ = Minimiser.Pair_Pair(d_943_a_, d_947_p1_)
            d_949_minim_ = Minimiser.default__.Minimise(d_948_vp_)
            d_950_listOfEdges_ = (d_949_minim_).GenerateReducedTailRec(0, _dafny.SeqWithoutIsStrInference([]))
            d_951_x_ = default__.NatBoolEdgesToCFGEdges(d_950_listOfEdges_, d_940_numToCFGNode_, (self).maxSegNum)
            d_952_miniCFG_ = BoolCFGraph_BoolCFGraph(d_951_x_, (self).maxSegNum)
            return d_952_miniCFG_
        elif True:
            return BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), (self).maxSegNum)

    def DOTPrintEdges(self, xe, fancyExits):
        d_953___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xe)) > (0):
                    d_953___accumulator_ = (d_953___accumulator_) + (((xe)[0]).DOTPrint(False))
                    in126_ = _this
                    in127_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    in128_ = fancyExits
                    _this = in126_
                    
                    xe = in127_
                    fancyExits = in128_
                    raise _dafny.TailCall()
                elif True:
                    return (d_953___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodes(self, xs, simpleOutput, g, printed):
        d_954___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(g)) > (0):
                    d_955_srctxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).src) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).src).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).src, (xs)[((((g)[0]).src).seg).v], simpleOutput)))
                    d_956_tgttxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).tgt) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).tgt).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).tgt, (xs)[((((g)[0]).tgt).seg).v], simpleOutput)))
                    d_954___accumulator_ = (d_954___accumulator_) + ((d_955_srctxt_) + (d_956_tgttxt_))
                    in129_ = _this
                    in130_ = xs
                    in131_ = simpleOutput
                    in132_ = _dafny.SeqWithoutIsStrInference((g)[1::])
                    in133_ = (printed) | (_dafny.Set({((g)[0]).src, ((g)[0]).tgt}))
                    _this = in129_
                    
                    xs = in130_
                    simpleOutput = in131_
                    g = in132_
                    printed = in133_
                    raise _dafny.TailCall()
                elif True:
                    return (d_954___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodeLabel(self, n, s, simpleOutput):
        if simpleOutput:
            d_957_lab_ = default__.DOTSeg(s, ((n).seg).v)
            d_958_nodeColour_ = default__.SegColour(s)
            return (((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_958_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + ((d_957_lab_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "> ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=<")))) + ((d_957_lab_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))
        elif True:
            d_959_lab_ = default__.DOTSegTable(s, ((n).seg).v)
            d_960_nodeColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_960_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + (d_959_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, xs, simpleOutput, fancyExits):
        d_961_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph CFG {\nnode [shape=box]\nnode[fontname=arial]\nedge[fontname=arial]\nranking=TB\n "))
        return (((d_961_prefix_) + ((self).DOTPrintNodes(xs, simpleOutput, (self).edges, _dafny.Set({})))) + ((self).DOTPrintEdges((self).edges, fancyExits))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n")))


class BoolCFGraph_BoolCFGraph(BoolCFGraph, NamedTuple('BoolCFGraph', [('edges', Any), ('maxSegNum', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolCFGraph.BoolCFGraph({_dafny.string_of(self.edges)}, {_dafny.string_of(self.maxSegNum)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolCFGraph_BoolCFGraph) and self.edges == __o.edges and self.maxSegNum == __o.maxSegNum
    def __hash__(self) -> int:
        return super().__hash__()

