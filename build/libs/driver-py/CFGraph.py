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
    def CountNodes(xe, seen):
        while True:
            with _dafny.label():
                if (len(xe)) == (0):
                    return len(seen)
                elif True:
                    in109_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    in110_ = (seen) | (_dafny.Set({((xe)[0]).src, ((xe)[0]).tgt}))
                    xe = in109_
                    seen = in110_
                    raise _dafny.TailCall()
                break

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
                    in111_ = d_864_p1_
                    in112_ = m
                    in113_ = maxSegNum
                    in114_ = (n) + (1)
                    p = in111_
                    m = in112_
                    maxSegNum = in113_
                    n = in114_
                    raise _dafny.TailCall()
                elif True:
                    return p
                break

    @staticmethod
    def SegNumPartition2(p, m, maxSegNum, n, xs):
        while True:
            with _dafny.label():
                if (n) <= (maxSegNum):
                    def lambda53_(d_866_m_, d_867_xs_, d_868_n_, d_869_p_):
                        def lambda54_(d_870_x_):
                            return (((((d_866_m_)[d_870_x_]).seg).is_Some) and (((((d_866_m_)[d_870_x_]).seg).v) < (len(d_867_xs_)))) and (((((d_866_m_)[d_870_x_]).seg) == (MiscTypes.Option_Some(d_868_n_))) and (default__.EquivSeg((d_867_xs_)[d_868_n_], (d_867_xs_)[(((d_866_m_)[d_870_x_]).seg).v])))

                        return lambda54_

                    d_865_f_ = lambda53_(m, xs, n, p)
                    d_871_p1_ = (p).SplitAt(d_865_f_, (len((p).elem)) - (1))
                    in115_ = d_871_p1_
                    in116_ = m
                    in117_ = maxSegNum
                    in118_ = (n) + (1)
                    in119_ = xs
                    p = in115_
                    m = in116_
                    maxSegNum = in117_
                    n = in118_
                    xs = in119_
                    raise _dafny.TailCall()
                elif True:
                    return p
                break

    @staticmethod
    def EquivSeg(s1, s2):
        source63_ = s1
        if source63_.is_JUMPSeg:
            d_872___mcc_h0_ = source63_.ins
            d_873___mcc_h1_ = source63_.lastIns
            d_874___mcc_h2_ = source63_.netOpEffect
            return ((((len((s1).Ins())) == (len((s2).Ins()))) and ((len((s2).Ins())) >= (2))) and ((((EVMConstants.default__.PUSH1) <= (((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode)) and ((((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode) == (((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode))) and ((((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode) <= (EVMConstants.default__.PUSH32)))) and ((_dafny.SeqWithoutIsStrInference(((s1).ins)[:(len((s1).ins)) - (1):])) == (_dafny.SeqWithoutIsStrInference(((s2).ins)[:(len((s2).ins)) - (1):])))
        elif source63_.is_JUMPISeg:
            d_875___mcc_h6_ = source63_.ins
            d_876___mcc_h7_ = source63_.lastIns
            d_877___mcc_h8_ = source63_.netOpEffect
            return ((((len((s1).Ins())) == (len((s2).Ins()))) and ((len((s2).Ins())) >= (2))) and ((((EVMConstants.default__.PUSH1) <= (((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode)) and ((((((s1).ins)[(len((s1).ins)) - (1)]).op).opcode) == (((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode))) and ((((((s2).ins)[(len((s1).ins)) - (1)]).op).opcode) <= (EVMConstants.default__.PUSH32)))) and ((_dafny.SeqWithoutIsStrInference(((s1).ins)[:(len((s1).ins)) - (1):])) == (_dafny.SeqWithoutIsStrInference(((s2).ins)[:(len((s2).ins)) - (1):])))
        elif source63_.is_RETURNSeg:
            d_878___mcc_h12_ = source63_.ins
            d_879___mcc_h13_ = source63_.lastIns
            d_880___mcc_h14_ = source63_.netOpEffect
            return ((s1).Ins()) == ((s2).Ins())
        elif source63_.is_STOPSeg:
            d_881___mcc_h18_ = source63_.ins
            d_882___mcc_h19_ = source63_.lastIns
            d_883___mcc_h20_ = source63_.netOpEffect
            return ((s1).Ins()) == ((s2).Ins())
        elif source63_.is_CONTSeg:
            d_884___mcc_h24_ = source63_.ins
            d_885___mcc_h25_ = source63_.lastIns
            d_886___mcc_h26_ = source63_.netOpEffect
            return ((s1).Ins()) == ((s2).Ins())
        elif True:
            d_887___mcc_h30_ = source63_.ins
            d_888___mcc_h31_ = source63_.lastIns
            d_889___mcc_h32_ = source63_.netOpEffect
            return ((s1).Ins()) == ((s2).Ins())

    @staticmethod
    def EdgesToMap(edges, seenNodes, reverseSeenNodes, builtMap, lastNum, index):
        while True:
            with _dafny.label():
                if (len(edges)) == (index):
                    return (lastNum, builtMap, seenNodes, reverseSeenNodes)
                elif True:
                    let_tmp_rhs0_ = (((seenNodes)[((edges)[index]).src], lastNum, seenNodes, reverseSeenNodes) if (((edges)[index]).src) in ((seenNodes).keys) else ((lastNum) + (1), (lastNum) + (1), (seenNodes).set(((edges)[index]).src, (lastNum) + (1)), (reverseSeenNodes).set((lastNum) + (1), ((edges)[index]).src)))
                    d_890_src_ = let_tmp_rhs0_[0]
                    d_891_last_ = let_tmp_rhs0_[1]
                    d_892_m1_ = let_tmp_rhs0_[2]
                    d_893_rm1_ = let_tmp_rhs0_[3]
                    let_tmp_rhs1_ = (((d_892_m1_)[((edges)[index]).tgt], d_891_last_, d_892_m1_, d_893_rm1_) if (((edges)[index]).tgt) in ((d_892_m1_).keys) else ((d_891_last_) + (1), (d_891_last_) + (1), (d_892_m1_).set(((edges)[index]).tgt, (d_891_last_) + (1)), (d_893_rm1_).set((d_891_last_) + (1), ((edges)[index]).tgt)))
                    d_894_tgt_ = let_tmp_rhs1_[0]
                    d_895_last_k_ = let_tmp_rhs1_[1]
                    d_896_m2_ = let_tmp_rhs1_[2]
                    d_897_rm2_ = let_tmp_rhs1_[3]
                    d_898_b_ = (builtMap).set((d_890_src_, ((edges)[index]).lab), d_894_tgt_)
                    in120_ = edges
                    in121_ = d_896_m2_
                    in122_ = d_897_rm2_
                    in123_ = d_898_b_
                    in124_ = d_895_last_k_
                    in125_ = (index) + (1)
                    edges = in120_
                    seenNodes = in121_
                    reverseSeenNodes = in122_
                    builtMap = in123_
                    lastNum = in124_
                    index = in125_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def BoolsToString(x):
        d_899___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_899___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "E")))
                elif True:
                    d_899___accumulator_ = (d_899___accumulator_) + (_dafny.SeqWithoutIsStrInference([(_dafny.CodePoint('1') if (x)[0] else _dafny.CodePoint('0'))]))
                    in126_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in126_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SegColour(s):
        source64_ = s
        if source64_.is_JUMPSeg:
            d_900___mcc_h0_ = source64_.ins
            d_901___mcc_h1_ = source64_.lastIns
            d_902___mcc_h2_ = source64_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif source64_.is_JUMPISeg:
            d_903___mcc_h6_ = source64_.ins
            d_904___mcc_h7_ = source64_.lastIns
            d_905___mcc_h8_ = source64_.netOpEffect
            return default__.branchColour
        elif source64_.is_RETURNSeg:
            d_906___mcc_h12_ = source64_.ins
            d_907___mcc_h13_ = source64_.lastIns
            d_908___mcc_h14_ = source64_.netOpEffect
            return default__.returnColour
        elif source64_.is_STOPSeg:
            d_909___mcc_h18_ = source64_.ins
            d_910___mcc_h19_ = source64_.lastIns
            d_911___mcc_h20_ = source64_.netOpEffect
            return default__.revertColour
        elif source64_.is_CONTSeg:
            d_912___mcc_h24_ = source64_.ins
            d_913___mcc_h25_ = source64_.lastIns
            d_914___mcc_h26_ = source64_.netOpEffect
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        elif True:
            d_915___mcc_h30_ = source64_.ins
            d_916___mcc_h31_ = source64_.lastIns
            d_917___mcc_h32_ = source64_.netOpEffect
            return default__.invalidColour

    @staticmethod
    def DOTSeg(s, numSeg):
        def iife16_(_pat_let8_0):
            def iife17_(d_919_r_):
                def lambda55_(source65_):
                    if source65_.is_Left:
                        d_920___mcc_h0_ = source65_.l
                        def iife18_(_pat_let9_0):
                            def iife19_(d_921_v_):
                                def lambda56_(source66_):
                                    if source66_.is_Value:
                                        d_922___mcc_h2_ = source66_.v
                                        def iife20_(_pat_let10_0):
                                            def iife21_(d_923_address_):
                                                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Constant 0x"))) + (Hex.default__.NatToHex(d_923_address_))
                                            return iife21_(_pat_let10_0)
                                        return iife20_(d_922___mcc_h2_)
                                    elif True:
                                        d_924___mcc_h3_ = source66_.s
                                        def iife22_(_pat_let11_0):
                                            def iife23_(d_925_msg_):
                                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Unknown"))
                                            return iife23_(_pat_let11_0)
                                        return iife22_(d_924___mcc_h3_)

                                return lambda56_(d_921_v_)
                            return iife19_(_pat_let9_0)
                        return iife18_(d_920___mcc_h0_)
                    elif True:
                        d_926___mcc_h1_ = source65_.r
                        def iife24_(_pat_let12_0):
                            def iife25_(d_927_stackPos_):
                                return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Stack on Entry.Peek("))) + (Int.default__.NatToString(d_927_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
                            return iife25_(_pat_let12_0)
                        return iife24_(d_926___mcc_h1_)

                return lambda55_(d_919_r_)
            return iife17_(_pat_let8_0)
        d_918_jumpTip_ = (iife16_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_928_stackSizeEffect_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Size &#916;: "))) + (Int.default__.IntToString((s).StackEffect()))
        d_929_mninNumOpe_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Stack Size on Entry &#8805; "))) + (Int.default__.NatToString((s).WeakestPreOperands(0)))
        d_930_prefix_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<B>Segment "))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</B><BR ALIGN=\"CENTER\"/>\n")))
        d_931_body_ = default__.DOTIns((s).Ins())
        return ((d_930_prefix_) + (d_931_body_), ((d_928_stackSizeEffect_) + (d_918_jumpTip_)) + (d_929_mninNumOpe_))

    @staticmethod
    def DOTSegTable(s, numSeg):
        def iife26_(_pat_let13_0):
            def iife27_(d_933_r_):
                def lambda57_(source67_):
                    if source67_.is_Left:
                        d_934___mcc_h0_ = source67_.l
                        def iife28_(_pat_let14_0):
                            def iife29_(d_935_v_):
                                def lambda58_(source68_):
                                    if source68_.is_Value:
                                        d_936___mcc_h2_ = source68_.v
                                        def iife30_(_pat_let15_0):
                                            def iife31_(d_937_address_):
                                                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Constant 0x"))) + (Hex.default__.NatToHex(d_937_address_))
                                            return iife31_(_pat_let15_0)
                                        return iife30_(d_936___mcc_h2_)
                                    elif True:
                                        d_938___mcc_h3_ = source68_.s
                                        def iife32_(_pat_let16_0):
                                            def iife33_(d_939_msg_):
                                                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Unknown"))
                                            return iife33_(_pat_let16_0)
                                        return iife32_(d_938___mcc_h3_)

                                return lambda58_(d_935_v_)
                            return iife29_(_pat_let14_0)
                        return iife28_(d_934___mcc_h0_)
                    elif True:
                        d_940___mcc_h1_ = source67_.r
                        def iife34_(_pat_let17_0):
                            def iife35_(d_941_stackPos_):
                                return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Exit Jump target: Stack on Entry.Peek("))) + (Int.default__.NatToString(d_941_stackPos_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))
                            return iife35_(_pat_let17_0)
                        return iife34_(d_940___mcc_h1_)

                return lambda57_(d_933_r_)
            return iife27_(_pat_let13_0)
        d_932_jumpTip_ = (iife26_(SegBuilder.default__.JUMPResolver(s)) if ((s).is_JUMPSeg) or ((s).is_JUMPISeg) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_942_tableStart_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE ALIGN=\"LEFT\" CELLBORDER=\"0\" BORDER=\"0\" cellpadding=\"0\"  CELLSPACING=\"1\">\n"))
        d_943_prefix_ = ((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD "))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">Segment ")))) + (Int.default__.NatToString(numSeg))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [0x")))) + (Hex.default__.NatToHex((s).StartAddress()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"\" tooltip=\"Stack Size &#916;: ")))) + (Int.default__.IntToString((s).StackEffect()))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#10;Stack Size on Entry &#8805; ")))) + (Int.default__.NatToString((s).WeakestPreOperands(0)))) + (d_932_jumpTip_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "><FONT color=\"green\">&#9636;</FONT></TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR><HR/>\n")))
        d_944_tableEnd_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>\n"))
        d_945_body_ = default__.DOTInsTable((s).Ins(), True)
        return (((d_942_tableStart_) + (d_943_prefix_)) + (d_945_body_)) + (d_944_tableEnd_)

    @staticmethod
    def DOTIns(xi):
        d_946___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_946___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_946___accumulator_ = (d_946___accumulator_) + (((xi)[0]).ToHTML())
                    in127_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in127_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DOTInsTable(xi, isFirst):
        d_947___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_947___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_948_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n"))
                    d_949_suffix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD></TR>\n"))
                    d_950_exitPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"exit\"")) if ((xi)[0]).IsJump() else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_951_entryPortTag_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "PORT=\"entry\"")) if isFirst else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                    d_952_a_ = ((xi)[0]).ToHTMLTable(d_951_entryPortTag_, d_950_exitPortTag_)
                    d_947___accumulator_ = (d_947___accumulator_) + (((d_948_prefix_) + (d_952_a_)) + (d_949_suffix_))
                    in128_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    in129_ = False
                    xi = in128_
                    isFirst = in129_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def NatBoolEdgesToCFGEdges(xs, m, maxSegNum):
        d_953___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_953___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_953___accumulator_ = (d_953___accumulator_) + (_dafny.SeqWithoutIsStrInference([BoolEdge_BoolEdge((m)[((xs)[0])[0]], ((xs)[0])[1], (m)[((xs)[0])[2]])]))
                    in130_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in131_ = m
                    in132_ = maxSegNum
                    xs = in130_
                    m = in131_
                    maxSegNum = in132_
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
        d_954_x_ = default__.BoolSeqToNat((self).id)
        return ((Int.default__.NatToString(d_954_x_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "_")))) + (Int.default__.NatToString(len((self).id)))


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
        d_955_lab1_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.jcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">jump</FONT>"))) if (self).lab else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + (default__.skcolour)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">skip</FONT>"))))
        d_956_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_956_labColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<")))) + (d_955_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, fancyExit):
        d_957_lab1_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Jump\",style=dashed")) if (self).lab else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Next\"")))
        d_958_labColour_ = (default__.jumpColour if (self).lab else default__.skipColour)
        d_959_exitPort_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":exit:se ")) if (fancyExit) and ((self).lab) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_960_entryPort_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":entry:w ")) if (fancyExit) and ((self).lab) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        return ((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + (((self).src).ToDot())) + (d_959_exitPort_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " -> s")))) + (((self).tgt).ToDot())) + (d_960_entryPort_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_957_lab1_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]\n")))


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
        def lambda59_(forall_var_10_):
            d_961_k_: int = forall_var_10_
            return not (((0) <= (d_961_k_)) and ((d_961_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_961_k_]).src).seg).is_Some) or (((((((self).edges)[d_961_k_]).src).seg).v) <= ((self).maxSegNum)))

        def lambda60_(forall_var_11_):
            d_962_k_: int = forall_var_11_
            return not (((0) <= (d_962_k_)) and ((d_962_k_) < (len((self).edges)))) or (not ((((((self).edges)[d_962_k_]).tgt).seg).is_Some) or (((((((self).edges)[d_962_k_]).tgt).seg).v) <= ((self).maxSegNum)))

        return (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda59_)) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).edges)), True, lambda60_))

    def Minimise(self, equiv, xs):
        d_963_r_ = default__.EdgesToMap((self).edges, _dafny.Map({CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0)): 0}), _dafny.Map({0: CFGNode_CFGNode(_dafny.SeqWithoutIsStrInference([]), MiscTypes.Option_Some(0))}), _dafny.Map({}), 0, 0)
        d_964_idToNum_ = (d_963_r_)[2]
        d_965_numToCFGNode_ = (d_963_r_)[3]
        d_966_lastStateNum_ = (d_963_r_)[0]
        d_967_transitions_ = (d_963_r_)[1]
        d_968_a_ = Automata.Auto_Auto((d_966_lastStateNum_) + (1), d_967_transitions_)
        if (d_966_lastStateNum_) > (0):
            def iife36_():
                coll1_ = _dafny.Set()
                compr_1_: int
                for compr_1_ in _dafny.IntegerRange(0, (d_966_lastStateNum_) + (1)):
                    d_970_q_: int = compr_1_
                    if ((0) <= (d_970_q_)) and ((d_970_q_) < ((d_966_lastStateNum_) + (1))):
                        coll1_ = coll1_.union(_dafny.Set([d_970_q_]))
                return _dafny.Set(coll1_)
            d_969_s_ = iife36_()

            d_971_p_ = PartitionMod.Partition_Partition((d_966_lastStateNum_) + (1), _dafny.SeqWithoutIsStrInference([d_969_s_]))
            d_972_p1_ = (default__.SegNumPartition2(d_971_p_, d_965_numToCFGNode_, (self).maxSegNum, 0, xs) if equiv else default__.SegNumPartition(d_971_p_, d_965_numToCFGNode_, (self).maxSegNum, 0))
            d_973_vp_ = Minimiser.Pair_Pair(d_968_a_, d_972_p1_)
            d_974_minim_ = Minimiser.default__.Minimise(d_973_vp_)
            d_975_listOfEdges_ = (d_974_minim_).GenerateReducedTailRec(0, _dafny.SeqWithoutIsStrInference([]))
            d_976_x_ = default__.NatBoolEdgesToCFGEdges(d_975_listOfEdges_, d_965_numToCFGNode_, (self).maxSegNum)
            d_977_miniCFG_ = BoolCFGraph_BoolCFGraph(d_976_x_, (self).maxSegNum)
            return d_977_miniCFG_
        elif True:
            return BoolCFGraph_BoolCFGraph(_dafny.SeqWithoutIsStrInference([]), (self).maxSegNum)

    def DOTPrintEdges(self, xe, fancyExits):
        d_978___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(xe)) > (0):
                    d_978___accumulator_ = (d_978___accumulator_) + (((xe)[0]).DOTPrint(False))
                    in133_ = _this
                    in134_ = _dafny.SeqWithoutIsStrInference((xe)[1::])
                    in135_ = fancyExits
                    _this = in133_
                    
                    xe = in134_
                    fancyExits = in135_
                    raise _dafny.TailCall()
                elif True:
                    return (d_978___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodes(self, xs, simpleOutput, g, printed):
        d_979___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(g)) > (0):
                    d_980_srctxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).src) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).src).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).src).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).src, (xs)[((((g)[0]).src).seg).v], simpleOutput)))
                    d_981_tgttxt_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")) if (((g)[0]).tgt) in (printed) else (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((((g)[0]).tgt).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) if ((((g)[0]).tgt).seg).is_None else (_this).DOTPrintNodeLabel(((g)[0]).tgt, (xs)[((((g)[0]).tgt).seg).v], simpleOutput)))
                    d_979___accumulator_ = (d_979___accumulator_) + ((d_980_srctxt_) + (d_981_tgttxt_))
                    in136_ = _this
                    in137_ = xs
                    in138_ = simpleOutput
                    in139_ = _dafny.SeqWithoutIsStrInference((g)[1::])
                    in140_ = (printed) | (_dafny.Set({((g)[0]).src, ((g)[0]).tgt}))
                    _this = in136_
                    
                    xs = in137_
                    simpleOutput = in138_
                    g = in139_
                    printed = in140_
                    raise _dafny.TailCall()
                elif True:
                    return (d_979___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                break

    def DOTPrintNodeLabel(self, n, s, simpleOutput):
        if simpleOutput:
            d_982_lab_ = default__.DOTSeg(s, ((n).seg).v)
            d_983_nodeColour_ = default__.SegColour(s)
            return (((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_983_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + ((d_982_lab_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "> ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=<")))) + ((d_982_lab_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))
        elif True:
            d_984_lab_ = default__.DOTSegTable(s, ((n).seg).v)
            d_985_nodeColour_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
            return ((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "s"))) + ((n).ToDot())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " [")))) + (d_985_nodeColour_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "label=<\n")))) + (d_984_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">]\n")))

    def DOTPrint(self, xs, simpleOutput, fancyExits):
        d_986_prefix_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "digraph CFG {\nnode [shape=box]\nnode[fontname=arial]\nedge[fontname=arial]\nranking=TB\n "))
        return (((d_986_prefix_) + ((self).DOTPrintNodes(xs, simpleOutput, (self).edges, _dafny.Set({})))) + ((self).DOTPrintEdges((self).edges, fancyExits))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}\n")))


class BoolCFGraph_BoolCFGraph(BoolCFGraph, NamedTuple('BoolCFGraph', [('edges', Any), ('maxSegNum', Any)])):
    def __dafnystr__(self) -> str:
        return f'CFGraph.BoolCFGraph.BoolCFGraph({_dafny.string_of(self.edges)}, {_dafny.string_of(self.maxSegNum)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, BoolCFGraph_BoolCFGraph) and self.edges == __o.edges and self.maxSegNum == __o.maxSegNum
    def __hash__(self) -> int:
        return super().__hash__()

