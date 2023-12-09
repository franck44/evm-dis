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
    def CountNodes(xe, seen):
        while True:
            with _dafny.label():
                if (len(xe)) == (0):
                    return len(seen)
                elif True:
                    in112_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    in113_ = (seen) | (_dafny.Set({((xe)[0]).src, ((xe)[0]).tgt}))
                    xe = in112_
                    seen = in113_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SegNumPartition(p, m, maxSegNum, n):
        while True:
            with _dafny.label():
                if (n) <= (maxSegNum):
                    def lambda57_(d_881_m_, d_882_n_, d_883_p_):
                        def lambda58_(d_884_x_):
                            return (((d_881_m_)[d_884_x_]).seg) == (MiscTypes.Option_Some(d_882_n_))

                        return lambda58_

                    d_880_f_ = lambda57_(m, n, p)
                    d_885_p1_ = (p).SplitAt(d_880_f_, (len((p).elem)) - (1))
                    in114_ = d_885_p1_
                    in115_ = m
                    in116_ = maxSegNum
                    in117_ = (n) + (1)
                    p = in114_
                    m = in115_
                    maxSegNum = in116_
                    n = in117_
                    raise _dafny.TailCall()
                elif True:
                    return p
                break

    @staticmethod
    def SegNumPartition2(p, m, maxSegNum, n, xs):
        while True:
            with _dafny.label():
                if (n) <= (maxSegNum):
                    def lambda59_(d_887_m_, d_888_xs_, d_889_n_, d_890_p_):
                        def lambda60_(d_891_x_):
                            return (((((d_887_m_)[d_891_x_]).seg).is_Some) and (((((d_887_m_)[d_891_x_]).seg).v) < (len(d_888_xs_)))) and (((((d_887_m_)[d_891_x_]).seg) == (MiscTypes.Option_Some(d_889_n_))) and (LinSegments.default__.EquivSeg((d_888_xs_)[d_889_n_], (d_888_xs_)[(((d_887_m_)[d_891_x_]).seg).v])))

                        return lambda60_

                    d_886_f_ = lambda59_(m, xs, n, p)
                    d_892_p1_ = (p).SplitAt(d_886_f_, (len((p).elem)) - (1))
                    in118_ = d_892_p1_
                    in119_ = m
                    in120_ = maxSegNum
                    in121_ = (n) + (1)
                    in122_ = xs
                    p = in118_
                    m = in119_
                    maxSegNum = in120_
                    n = in121_
                    xs = in122_
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
                    d_893_src_ = let_tmp_rhs0_[0]
                    d_894_last_ = let_tmp_rhs0_[1]
                    d_895_m1_ = let_tmp_rhs0_[2]
                    d_896_rm1_ = let_tmp_rhs0_[3]
                    let_tmp_rhs1_ = (((d_895_m1_)[((edges)[index]).tgt], d_894_last_, d_895_m1_, d_896_rm1_) if (((edges)[index]).tgt) in ((d_895_m1_).keys) else ((d_894_last_) + (1), (d_894_last_) + (1), (d_895_m1_).set(((edges)[index]).tgt, (d_894_last_) + (1)), (d_896_rm1_).set((d_894_last_) + (1), ((edges)[index]).tgt)))
                    d_897_tgt_ = let_tmp_rhs1_[0]
                    d_898_last_k_ = let_tmp_rhs1_[1]
                    d_899_m2_ = let_tmp_rhs1_[2]
                    d_900_rm2_ = let_tmp_rhs1_[3]
                    d_901_b_ = (builtMap).set((d_893_src_, ((edges)[index]).lab), d_897_tgt_)
                    in123_ = edges
                    in124_ = d_899_m2_
                    in125_ = d_900_rm2_
                    in126_ = d_901_b_
                    in127_ = d_898_last_k_
                    in128_ = (index) + (1)
                    edges = in123_
                    seenNodes = in124_
                    reverseSeenNodes = in125_
                    builtMap = in126_
                    lastNum = in127_
                    index = in128_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def BoolsToString(x):
        d_902___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_902___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "E")))
                elif True:
                    d_902___accumulator_ = (d_902___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_dafny.CodePoint('1') if (x)[0] else _dafny.CodePoint('0'))]))
                    in129_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in129_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SegColour(s):
        source64_ = s
        if source64_.is_JUMPSeg:
            d_903___mcc_h0_ = source64_.ins
            d_904___mcc_h1_ = source64_.lastIns
            d_905___mcc_h2_ = source64_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif source64_.is_JUMPISeg:
            d_906___mcc_h6_ = source64_.ins
            d_907___mcc_h7_ = source64_.lastIns
            d_908___mcc_h8_ = source64_.netOpEffect
            return default__.branchColour
        elif source64_.is_RETURNSeg:
            d_909___mcc_h12_ = source64_.ins
            d_910___mcc_h13_ = source64_.lastIns
            d_911___mcc_h14_ = source64_.netOpEffect
            return default__.returnColour
        elif source64_.is_STOPSeg:
            d_912___mcc_h18_ = source64_.ins
            d_913___mcc_h19_ = source64_.lastIns
            d_914___mcc_h20_ = source64_.netOpEffect
            return default__.revertColour
        elif source64_.is_CONTSeg:
            d_915___mcc_h24_ = source64_.ins
            d_916___mcc_h25_ = source64_.lastIns
            d_917___mcc_h26_ = source64_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif True:
            d_918___mcc_h30_ = source64_.ins
            d_919___mcc_h31_ = source64_.lastIns
            d_920___mcc_h32_ = source64_.netOpEffect
            return default__.invalidColour

    @staticmethod
    def DOTSeg(s, numSeg):
        def iife14_(_pat_let7_0):
            def iife15_(d_922_r_):
                def lambda61_(source65_):
                    if source65_.is_Left:
                        d_923___mcc_h0_ = source65_.l
                        def iife16_(_pat_let8_0):
                            def iife17_(d_924_v_):
                                def lambda62_(source66_):
                                    if source66_.is_Value:
                                        d_925___mcc_h2_ = source66_.v
                                        def iife18_(_pat_let9_0):
                                            def iife19_(d_926_address_):
                                                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Constant 0x"))) + (Hex.default__.NatToHex(d_926_address_))
                                            return iife19_(_pat_let9_0)
                                        return iife18_(d_925___mcc_h2_)
                                    elif True:
                                        d_927___mcc_h3_ = source66_.s
                                        def iife20_(_pat_let10_0):
                                            def iife21_(d_928_msg_):
                                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Unknown"))
                                            return iife21_(_pat_let10_0)
                                        return iife20_(d_927___mcc_h3_)

                                return lambda62_(d_924_v_)
                            return iife17_(_pat_let8_0)
                        return iife16_(d_923___mcc_h0_)
                    elif True:
                        d_929___mcc_h1_ = source65_.r
                        def iife22_(_pat_let11_0):
                            def iife23_(d_930_stackPos_):
                                return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Stack on Entry.Peek("))) + (Int.default__.NatToString(d_930_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
                            return iife23_(_pat_let11_0)
                        return iife22_(d_929___mcc_h1_)

                return lambda61_(d_922_r_)
            return iife15_(_pat_let7_0)
        d_921_jumpTip_ = (iife14_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_931_stackSizeEffect_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size &#916;: "))) + (Int.default__.IntToString((s).StackEffect()))
        d_932_mninNumOpe_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Stack Size on Entry &#8805; "))) + (Int.default__.NatToString((s).WeakestPreOperands(0)))
        d_933_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</B><BR ALIGN=\"CENTER\"/>\n")))
        d_934_body_ = default__.DOTIns((s).Ins())
        return ((d_933_prefix_) + (d_934_body_), ((d_931_stackSizeEffect_) + (d_921_jumpTip_)) + (d_932_mninNumOpe_))

    @staticmethod
    def DOTSegTable(s, numSeg):
        def iife24_(_pat_let12_0):
            def iife25_(d_936_r_):
                def lambda63_(source67_):
                    if source67_.is_Left:
                        d_937___mcc_h0_ = source67_.l
                        def iife26_(_pat_let13_0):
                            def iife27_(d_938_v_):
                                def lambda64_(source68_):
                                    if source68_.is_Value:
                                        d_939___mcc_h2_ = source68_.v
                                        def iife28_(_pat_let14_0):
                                            def iife29_(d_940_address_):
                                                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Constant 0x"))) + (Hex.default__.NatToHex(d_940_address_))
                                            return iife29_(_pat_let14_0)
                                        return iife28_(d_939___mcc_h2_)
                                    elif True:
                                        d_941___mcc_h3_ = source68_.s
                                        def iife30_(_pat_let15_0):
                                            def iife31_(d_942_msg_):
                                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Unknown"))
                                            return iife31_(_pat_let15_0)
                                        return iife30_(d_941___mcc_h3_)

                                return lambda64_(d_938_v_)
                            return iife27_(_pat_let13_0)
                        return iife26_(d_937___mcc_h0_)
                    elif True:
                        d_943___mcc_h1_ = source67_.r
                        def iife32_(_pat_let16_0):
                            def iife33_(d_944_stackPos_):
                                return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Stack on Entry.Peek("))) + (Int.default__.NatToString(d_944_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
                            return iife33_(_pat_let16_0)
                        return iife32_(d_943___mcc_h1_)

                return lambda63_(d_936_r_)
            return iife25_(_pat_let12_0)
        d_935_jumpTip_ = (iife24_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_945_tableStart_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE ALIGN=\"LEFT\" CELLBORDER=\"0\" BORDER=\"0\" cellpadding=\"0\"  CELLSPACING=\"1\">\n"))
        d_946_prefix_ = ((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">Segment ")))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"\" tooltip=\"Stack Size &#916;: ")))) + (Int.default__.IntToString((s).StackEffect()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Stack Size on Entry &#8805; ")))) + (Int.default__.NatToString((s).WeakestPreOperands(0)))) + (d_935_jumpTip_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "><FONT color=\"green\">&#9636;</FONT></TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR><HR/>\n")))
        d_947_tableEnd_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>\n"))
        d_948_body_ = default__.DOTInsTable((s).Ins(), True)
        return (((d_945_tableStart_) + (d_946_prefix_)) + (d_948_body_)) + (d_947_tableEnd_)

    @staticmethod
    def DOTIns(xi):
        d_949___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_949___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_949___accumulator_ = (d_949___accumulator_) + (((xi)[0]).ToHTML())
                    in130_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in130_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DOTInsTable(xi, isFirst):
        d_950___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_950___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_951_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n"))
                    d_952_suffix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD></TR>\n"))
                    d_953_exitPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"exit\"")) if ((xi)[0]).IsJump() else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_954_entryPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"entry\"")) if isFirst else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_955_a_ = ((xi)[0]).ToHTMLTable(d_954_entryPortTag_, d_953_exitPortTag_)
                    d_950___accumulator_ = (d_950___accumulator_) + (((d_951_prefix_) + (d_955_a_)) + (d_952_suffix_))
                    in131_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    in132_ = False
                    xi = in131_
                    isFirst = in132_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def NatBoolEdgesToCFGEdges(xs, m, maxSegNum):
        d_956___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_956___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_956___accumulator_ = (d_956___accumulator_) + (_dafny.SeqWithoutIsStrInference([BoolEdge_BoolEdge((m)[((xs)[0])[0]], ((xs)[0])[1], (m)[((xs)[0])[2]])]))
                    in133_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in134_ = m
                    in135_ = maxSegNum
                    xs = in133_
                    m = in134_
                    maxSegNum = in135_
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
        d_957_x_ = default__.BoolSeqToNat((self).id)
        return ((Int.default__.NatToString(d_957_x_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "_")))) + (Int.default__.NatToString(len((self).id)))


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
        d_958_lab1_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.jcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">jump</FONT>"))) if (self).lab else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.skcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">skip</FONT>"))))
        d_959_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_959_labColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<")))) + (d_958_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, fancyExit):
        d_960_lab1_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Jump\",style=dashed")) if (self).lab else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Next\"")))
        d_961_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        d_962_exitPort_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":exit:se ")) if (fancyExit) and ((self).lab) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_963_entryPort_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":entry:w ")) if (fancyExit) and ((self).lab) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToDot())) + (d_962_exitPort_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToDot())) + (d_963_entryPort_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_960_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))


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

    def NumNodes(self):
        return default__.CountNodes((self).edges, _dafny.Set({}))

    def NumEdges(self):
        return len((self).edges)

    def IsValid(self):
        def lambda65_(forall_var_16_):
            d_964_k_: int = forall_var_16_
            return not (((0) <= (d_964_k_)) and ((d_964_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_964_k_]).src).seg).is_Some) or (((((((self).edges)[d_964_k_]).src).seg).v) <= ((self).maxSegNum)))

        def lambda66_(forall_var_17_):
            d_965_k_: int = forall_var_17_
            return not (((0) <= (d_965_k_)) and ((d_965_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_965_k_]).tgt).seg).is_Some) or (((((((self).edges)[d_965_k_]).tgt).seg).v) <= ((self).maxSegNum)))

        return (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda65_)) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda66_))

    def Minimise(self, equiv, xs):
        d_966_r_ = default__.EdgesToMap((self).edges, _dafny.Map({CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0)): 0}), _dafny.Map({0: CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}), _dafny.Map({}), 0, 0)
        d_967_idToNum_ = (d_966_r_)[2]
        d_968_numToCFGNode_ = (d_966_r_)[3]
        d_969_lastStateNum_ = (d_966_r_)[0]
        d_970_transitions_ = (d_966_r_)[1]
        d_971_a_ = Automata.Auto_Auto((d_969_lastStateNum_) + (1), d_970_transitions_)
        if (d_969_lastStateNum_) > (0):
            def iife34_():
                coll1_ = _dafny.Set()
                compr_1_: int
                for compr_1_ in _dafny.IntegerRange(0, (d_969_lastStateNum_) + (1)):
                    d_973_q_: int = compr_1_
                    if ((0) <= (d_973_q_)) and ((d_973_q_) < ((d_969_lastStateNum_) + (1))):
                        coll1_ = coll1_.union(_dafny.Set([d_973_q_]))
                return _dafny.Set(coll1_)
            d_972_s_ = iife34_()

            d_974_p_ = PartitionMod.Partition_Partition((d_969_lastStateNum_) + (1), _dafny.SeqWithoutIsStrInference([d_972_s_]))
            d_975_p1_ = (default__.SegNumPartition2(d_974_p_, d_968_numToCFGNode_, (self).maxSegNum, 0, xs) if equiv else default__.SegNumPartition(d_974_p_, d_968_numToCFGNode_, (self).maxSegNum, 0))
            d_976_vp_ = Minimiser.Pair_Pair(d_971_a_, d_975_p1_)
            d_977_minim_ = Minimiser.default__.Minimise(d_976_vp_)
            d_978_listOfEdges_ = (d_977_minim_).GenerateReducedTailRec(0, _dafny.SeqWithoutIsStrInference([]))
            d_979_x_ = default__.NatBoolEdgesToCFGEdges(d_978_listOfEdges_, d_968_numToCFGNode_, (self).maxSegNum)
            d_980_miniCFG_ = BoolCFGraph_BoolCFGraph(d_979_x_, (self).maxSegNum)
            return d_980_miniCFG_
        elif True:
            return BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), (self).maxSegNum)

    def DOTPrintEdges(self, xe, fancyExits):
        d_981___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xe)) > (0):
                    d_981___accumulator_ = (d_981___accumulator_) + (((xe)[0]).DOTPrint(False))
                    in136_ = _this
                    in137_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    in138_ = fancyExits
                    _this = in136_
                    
                    xe = in137_
                    fancyExits = in138_
                    raise _dafny.TailCall()
                elif True:
                    return (d_981___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodes(self, xs, simpleOutput, g, printed):
        d_982___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(g)) > (0):
                    d_983_srctxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).src) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).src).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).src, (xs)[((((g)[0]).src).seg).v], simpleOutput)))
                    d_984_tgttxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).tgt) in ((printed) | (_dafny.Set({((g)[0]).src}))) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).tgt).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).tgt, (xs)[((((g)[0]).tgt).seg).v], simpleOutput)))
                    d_982___accumulator_ = (d_982___accumulator_) + ((d_983_srctxt_) + (d_984_tgttxt_))
                    in139_ = _this
                    in140_ = xs
                    in141_ = simpleOutput
                    in142_ = _dafny.SeqWithoutIsStrInference((g)[1::])
                    in143_ = (printed) | (_dafny.Set({((g)[0]).src, ((g)[0]).tgt}))
                    _this = in139_
                    
                    xs = in140_
                    simpleOutput = in141_
                    g = in142_
                    printed = in143_
                    raise _dafny.TailCall()
                elif True:
                    return (d_982___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodeLabel(self, n, s, simpleOutput):
        if simpleOutput:
            d_985_lab_ = default__.DOTSeg(s, ((n).seg).v)
            d_986_nodeColour_ = default__.SegColour(s)
            return (((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_986_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + ((d_985_lab_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "> ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=<")))) + ((d_985_lab_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))
        elif True:
            d_987_lab_ = default__.DOTSegTable(s, ((n).seg).v)
            d_988_nodeColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_988_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + (d_987_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, xs, simpleOutput, fancyExits):
        d_989_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph CFG {\nnode [shape=box]\nnode[fontname=arial]\nedge[fontname=arial]\nranking=TB\n "))
        return (((d_989_prefix_) + ((self).DOTPrintNodes(xs, simpleOutput, (self).edges, _dafny.Set({})))) + ((self).DOTPrintEdges((self).edges, fancyExits))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n")))


class BoolCFGraph_BoolCFGraph(BoolCFGraph, NamedTuple('BoolCFGraph', [('edges', Any), ('maxSegNum', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolCFGraph.BoolCFGraph({_dafny.string_of(self.edges)}, {_dafny.string_of(self.maxSegNum)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolCFGraph_BoolCFGraph) and self.edges == __o.edges and self.maxSegNum == __o.maxSegNum
    def __hash__(self) -> int:
        return super().__hash__()

