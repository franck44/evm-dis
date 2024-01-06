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
import CFGState
import Automata
import SeqOfSets
import PartitionMod
import GStateMinimiser
import Statistics
import HTML

# Module: EVMObject

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def CollectJumpDests(xs):
        d_905___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_905___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_905___accumulator_ = (d_905___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in115_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in115_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CollectThem(xs):
        return default__.CollectPCToSeg(xs, _dafny.Map({}), 0)

    @staticmethod
    def CollectPCToSeg(xs, m, index):
        while True:
            with _dafny.label():
                if (index) == (len(xs)):
                    return m
                elif True:
                    in116_ = xs
                    in117_ = (m).set(((xs)[index]).StartAddress(), index)
                    in118_ = (index) + (1)
                    xs = in116_
                    m = in117_
                    index = in118_
                    raise _dafny.TailCall()
                break


class Path:
    @classmethod
    def default(cls, ):
        return lambda: Path_Path(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Path(self) -> bool:
        return isinstance(self, Path_Path)

class Path_Path(Path, NamedTuple('Path', [('states', Any), ('exits', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMObject.Path.Path({_dafny.string_of(self.states)}, {_dafny.string_of(self.exits)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Path_Path) and self.states == __o.states and self.exits == __o.exits
    def __hash__(self) -> int:
        return super().__hash__()


class ValidSeqValidLinSeg:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class ValidEVMObj:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return EVMObj_EVMObj(_dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]), default__.CollectThem(_dafny.SeqWithoutIsStrInference([])))

class EVMObj:
    @classmethod
    def default(cls, ):
        return lambda: EVMObj_EVMObj(_dafny.Seq({}), _dafny.Seq({}), _dafny.Map({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_EVMObj(self) -> bool:
        return isinstance(self, EVMObj_EVMObj)
    def StartAddress(self, i):
        return (((self).xs)[i]).StartAddress()

    def Size(self, ls):
        d_906___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (len(ls)) == (0):
                    return (0) + (d_906___accumulator_)
                elif True:
                    d_906___accumulator_ = (d_906___accumulator_) + (((ls)[0]).Size(((ls)[0]).Ins()))
                    in119_ = _this
                    in120_ = _dafny.SeqWithoutIsStrInference((ls)[1::])
                    _this = in119_
                    
                    ls = in120_
                    raise _dafny.TailCall()
                break

    def NextG(self, s):
        source60_ = s
        if source60_.is_EGState:
            d_907___mcc_h0_ = source60_.segNum
            d_908___mcc_h1_ = source60_.st
            d_909_st_ = d_908___mcc_h1_
            d_910_segNum_ = d_907___mcc_h0_
            d_911_srcSeg_ = ((self).xs)[d_910_segNum_]
            d_912_src_ = State.AState_EState((d_911_srcSeg_).StartAddress(), d_909_st_)
            d_913_successors_ = _dafny.SeqWithoutIsStrInference([(d_911_srcSeg_).Run(d_912_src_, d_914_i_, (self).jumpDests) for d_914_i_ in range((d_911_srcSeg_).NumberOfExits())])
            def lambda45_(d_916_s_k_):
                def lambda46_(source61_):
                    if source61_.is_EState:
                        d_917___mcc_h3_ = source61_.pc
                        d_918___mcc_h4_ = source61_.stack
                        d_919_st_ = d_918___mcc_h4_
                        d_920_pc_ = d_917___mcc_h3_
                        if (d_920_pc_) in ((self).PCToSegMap):
                            return CFGState.GState_EGState(((self).PCToSegMap)[d_920_pc_], (d_916_s_k_).stack)
                        elif True:
                            return CFGState.GState_ErrorGState(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "NextG:  "))) + (Int.default__.NatToString(d_920_pc_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " not defined"))))
                    elif True:
                        d_921___mcc_h5_ = source61_.msg
                        d_922_msg_ = d_921___mcc_h5_
                        return CFGState.GState_ErrorGState(d_922_msg_)

                return lambda46_(d_916_s_k_)

            d_915_succGStates_ = MiscTypes.default__.Map(d_913_successors_, lambda45_)
            return d_915_succGStates_
        elif True:
            d_923___mcc_h2_ = source60_.msg
            return _dafny.SeqWithoutIsStrInference([])

    def RunAll(self, exits, s):
        _this = self
        while True:
            with _dafny.label():
                if (len(exits)) == (0):
                    return s
                elif ((s).pc) in ((_this).PCToSegMap):
                    d_924_seg_ = ((_this).PCToSegMap)[(s).pc]
                    if ((((_this).xs)[d_924_seg_]).NumberOfExits()) > ((exits)[0]):
                        d_925_s_k_ = (((_this).xs)[d_924_seg_]).Run(s, (exits)[0], (_this).jumpDests)
                        if (d_925_s_k_).is_EState:
                            in121_ = _this
                            in122_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                            in123_ = d_925_s_k_
                            _this = in121_
                            
                            exits = in122_
                            s = in123_
                            raise _dafny.TailCall()
                        elif True:
                            return State.AState_Error(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Successor state of "))) + ((s).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " is not an EState"))))
                    elif True:
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit does not exist")))
                elif True:
                    return State.AState_Error((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found for state "))) + ((s).ToString()))
                break

    def PreservesCond(self, c, exits, initpc):
        pat_let_tv5_ = initpc
        def iife22_(_pat_let10_0):
            def iife23_(d_927_dt__update__tmp_h0_):
                def iife24_(_pat_let11_0):
                    def iife25_(d_928_dt__update_hpc_h0_):
                        return State.AState_EState(d_928_dt__update_hpc_h0_, (d_927_dt__update__tmp_h0_).stack)
                    return iife25_(_pat_let11_0)
                return iife24_(pat_let_tv5_)
            return iife23_(_pat_let10_0)
        d_926_initState_ = iife22_(State.default__.BuildInitState(c, 0))
        d_929_endState_ = (self).RunAll(exits, d_926_initState_)
        if (d_929_endState_).is_EState:
            return (d_929_endState_).Sat(c)
        elif True:
            return False

    def SafeLoopFound(self, i, pStates, pExits):
        _this = self
        while True:
            with _dafny.label():
                source62_ = (_this).FindFirstNodeWithSegIndex(i, pStates, 0)
                if source62_.is_None:
                    return MiscTypes.Option_None()
                elif True:
                    d_930___mcc_h0_ = source62_.v
                    d_931_index_ = d_930___mcc_h0_
                    d_932_pathFromIndex_ = _dafny.SeqWithoutIsStrInference((pStates)[d_931_index_::])
                    d_933_exitsFromIndex_ = _dafny.SeqWithoutIsStrInference((pExits)[d_931_index_::])
                    d_934_segmentsOnPathFromIndex_ = _dafny.SeqWithoutIsStrInference([((d_932_pathFromIndex_)[d_935_i_]).segNum for d_935_i_ in range(len(d_932_pathFromIndex_))])
                    d_936_tgtCond_ = (((_this).xs)[(MiscTypes.default__.Last(pStates)).segNum]).LeadsTo((((_this).xs)[i]).StartAddress(), MiscTypes.default__.Last(pExits))
                    d_937_w1_ = LinSegments.default__.WPreSeqSegs(d_934_segmentsOnPathFromIndex_, d_933_exitsFromIndex_, d_936_tgtCond_, (_this).xs, (((_this).xs)[i]).StartAddress())
                    if (d_937_w1_).is_StTrue:
                        return MiscTypes.Option_Some(d_931_index_)
                    elif (d_937_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif (_this).PreservesCond(d_937_w1_, d_933_exitsFromIndex_, (((_this).xs)[i]).StartAddress()):
                        return MiscTypes.Option_Some(d_931_index_)
                    elif (0) < (len(d_932_pathFromIndex_)):
                        in124_ = _this
                        in125_ = i
                        in126_ = _dafny.SeqWithoutIsStrInference((d_932_pathFromIndex_)[1::])
                        in127_ = _dafny.SeqWithoutIsStrInference((d_933_exitsFromIndex_)[1::])
                        _this = in124_
                        
                        i = in125_
                        pStates = in126_
                        pExits = in127_
                        raise _dafny.TailCall()
                    elif True:
                        return MiscTypes.Option_None()
                break

    def FindFirstNodeWithSegIndex(self, i, gs, index):
        _this = self
        while True:
            with _dafny.label():
                if (len(gs)) == (index):
                    return MiscTypes.Option_None()
                elif True:
                    source63_ = (gs)[index]
                    if source63_.is_EGState:
                        d_938___mcc_h0_ = source63_.segNum
                        d_939___mcc_h1_ = source63_.st
                        d_940_st_ = d_939___mcc_h1_
                        d_941_i_k_ = d_938___mcc_h0_
                        if (d_941_i_k_) == (i):
                            return MiscTypes.Option_Some(index)
                        elif True:
                            in128_ = _this
                            in129_ = i
                            in130_ = gs
                            in131_ = (index) + (1)
                            _this = in128_
                            
                            i = in129_
                            gs = in130_
                            index = in131_
                            raise _dafny.TailCall()
                    elif True:
                        d_942___mcc_h2_ = source63_.msg
                        d_943_m_ = d_942___mcc_h2_
                        return MiscTypes.Option_None()
                break

    def DFS(self, p, a, maxDepth, debugInfo, stats):
        a_k: Automata.Auto = Automata.ValidAuto.default()
        stats_k: Statistics.Stats = Statistics.Stats.default()()
        d_944_lastOnPath_: CFGState.GState
        d_944_lastOnPath_ = MiscTypes.default__.Last((p).states)
        if ((maxDepth) == (0)) or ((d_944_lastOnPath_).is_ErrorGState):
            d_945_stats_k_: Statistics.Stats
            d_945_stats_k_ = ((stats).SetMaxDepth() if (maxDepth) == (0) else stats)
            rhs0_ = a
            rhs1_ = d_945_stats_k_
            a_k = rhs0_
            stats_k = rhs1_
            return a_k, stats_k
        elif True:
            a_k = a
            stats_k = stats
            hi4_ = len((self).NextG(d_944_lastOnPath_))
            for d_946_i_ in range(0, hi4_):
                d_947_i__th__succ_: CFGState.GState
                d_947_i__th__succ_ = ((self).NextG(d_944_lastOnPath_))[d_946_i_]
                if (d_947_i__th__succ_).is_ErrorGState:
                    rhs2_ = (a_k).AddEdge(d_944_lastOnPath_, d_947_i__th__succ_)
                    rhs3_ = (stats_k).IncError()
                    a_k = rhs2_
                    stats_k = rhs3_
                elif (d_947_i__th__succ_) in ((a_k).indexOf):
                    rhs4_ = (a_k).AddEdge(d_944_lastOnPath_, ((a_k).states)[((a_k).indexOf)[d_947_i__th__succ_]])
                    rhs5_ = (stats_k).IncVisited()
                    a_k = rhs4_
                    stats_k = rhs5_
                elif not((((self).xs)[(d_944_lastOnPath_).segNum]).IsJump()):
                    d_948_j_: Automata.Auto
                    d_948_j_ = (a_k).AddEdge(d_944_lastOnPath_, d_947_i__th__succ_)
                    d_949_p_k_: Path
                    d_949_p_k_ = Path_Path(((p).states) + (_dafny.SeqWithoutIsStrInference([d_947_i__th__succ_])), ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_946_i_])))
                    out0_: Automata.Auto
                    out1_: Statistics.Stats
                    out0_, out1_ = (self).DFS(d_949_p_k_, d_948_j_, (maxDepth) - (1), debugInfo, stats_k)
                    a_k = out0_
                    stats_k = out1_
                elif True:
                    source64_ = (self).SafeLoopFound((d_947_i__th__succ_).segNum, (p).states, ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_946_i_])))
                    if source64_.is_None:
                        out2_: Automata.Auto
                        out3_: Statistics.Stats
                        out2_, out3_ = (self).DFS(Path_Path(((p).states) + (_dafny.SeqWithoutIsStrInference([d_947_i__th__succ_])), ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_946_i_]))), (a_k).AddEdge(d_944_lastOnPath_, d_947_i__th__succ_), (maxDepth) - (1), debugInfo, stats_k)
                        a_k = out2_
                        stats_k = out3_
                    elif True:
                        d_950___mcc_h0_ = source64_.v
                        d_951_index_ = d_950___mcc_h0_
                        rhs6_ = (a_k).AddEdge(d_944_lastOnPath_, ((p).states)[d_951_index_])
                        rhs7_ = (stats_k).IncWpre()
                        a_k = rhs6_
                        stats_k = rhs7_
        return a_k, stats_k

    def BuildCFG(self, maxDepth, minimise):
        a: Automata.Auto = Automata.ValidAuto.default()
        stats: Statistics.Stats = Statistics.Stats.default()()
        d_952_a1_: Automata.Auto
        d_953_s1_: Statistics.Stats
        out4_: Automata.Auto
        out5_: Statistics.Stats
        out4_, out5_ = (self).DFS(Path_Path(_dafny.SeqWithoutIsStrInference([CFGState.default__.DEFAULT__GSTATE]), _dafny.SeqWithoutIsStrInference([])), (Automata.Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({}))).AddState(CFGState.default__.DEFAULT__GSTATE), maxDepth, True, Statistics.Stats_Stats(False, 0, 0, 0, (0, 0)))
        d_952_a1_ = out4_
        d_953_s1_ = out5_
        if (not(minimise)) or (((d_952_a1_).SSize()) == (0)):
            rhs8_ = d_952_a1_
            rhs9_ = d_953_s1_
            a = rhs8_
            stats = rhs9_
            return a, stats
        elif True:
            d_954_p1_: PartitionMod.Partition
            d_954_p1_ = PartitionMod.default__.MakeInit((d_952_a1_).SSize())
            d_955_e_: Callable
            def lambda47_(d_956_a1_):
                def lambda48_(d_957_x_, d_958_y_):
                    def lambda49_(source65_):
                        d_959___mcc_h0_ = source65_[0]
                        d_960___mcc_h1_ = source65_[1]
                        source66_ = d_959___mcc_h0_
                        if source66_.is_EGState:
                            d_961___mcc_h2_ = source66_.segNum
                            d_962___mcc_h3_ = source66_.st
                            source67_ = d_960___mcc_h1_
                            if source67_.is_EGState:
                                d_963___mcc_h6_ = source67_.segNum
                                d_964___mcc_h7_ = source67_.st
                                d_965_s2_ = d_963___mcc_h6_
                                d_966_s1_ = d_961___mcc_h2_
                                return (d_966_s1_) == (d_965_s2_)
                            elif True:
                                d_967___mcc_h10_ = source67_.msg
                                return False
                        elif True:
                            d_968___mcc_h12_ = source66_.msg
                            return False

                    return (True if (d_957_x_) == (d_958_y_) else lambda49_((((d_956_a1_).states)[d_957_x_], ((d_956_a1_).states)[d_958_y_])))

                return lambda48_

            d_955_e_ = lambda47_(d_952_a1_)
            d_969_p2_: PartitionMod.Partition
            d_969_p2_ = (d_954_p1_).ComputeFinest(d_955_e_)
            d_970_vp_: GStateMinimiser.Pair
            d_970_vp_ = GStateMinimiser.Pair_Pair(d_952_a1_, d_969_p2_)
            d_971_a2_: Automata.Auto
            d_971_a2_ = (d_970_vp_).Minimise()
            pat_let_tv6_ = d_952_a1_
            pat_let_tv7_ = d_952_a1_
            def iife26_(_pat_let12_0):
                def iife27_(d_972_dt__update__tmp_h0_):
                    def iife28_(_pat_let13_0):
                        def iife29_(d_973_dt__update_hnonMinimisedSize_h0_):
                            return Statistics.Stats_Stats((d_972_dt__update__tmp_h0_).maxDepthReached, (d_972_dt__update__tmp_h0_).visitedStates, (d_972_dt__update__tmp_h0_).wPreInvSuccess, (d_972_dt__update__tmp_h0_).errorState, d_973_dt__update_hnonMinimisedSize_h0_)
                        return iife29_(_pat_let13_0)
                    return iife28_(((pat_let_tv6_).SSize(), (pat_let_tv7_).TSize(0)))
                return iife27_(_pat_let12_0)
            rhs10_ = d_971_a2_
            rhs11_ = iife26_(d_953_s1_)
            a = rhs10_
            stats = rhs11_
            return a, stats
        return a, stats

    def ToHTML(self, a, withTable, minStackSizeForState):
        if (a).is_ErrorGState:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"))
        elif withTable:
            return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<"))) + (HTML.default__.DOTSegTable(((self).xs)[(a).segNum], (a).segNum, minStackSizeForState))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))
        elif True:
            return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<"))) + ((HTML.default__.DOTSeg(((self).xs)[(a).segNum], (a).segNum, minStackSizeForState))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))

    def DotLabel(self, s, exit):
        d_974_lab_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")) if (s).is_ErrorGState else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Jump\",style=dashed")) if ((((self).xs)[(s).segNum]).IsJump()) and ((exit) == (((((self).xs)[(s).segNum]).NumberOfExits()) - (1))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Next\""))) if ((s).is_EGState) and ((exit) < ((((self).xs)[(s).segNum]).NumberOfExits())) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error Number of exits"))))
        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ["))) + (d_974_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))

    def Fix(self, a, wpre0, xu, xc, maxIter):
        _this = self
        while True:
            with _dafny.label():
                if (xu) == (_dafny.Set({})):
                    return MiscTypes.Either_Left(xc)
                elif (maxIter) == (0):
                    return MiscTypes.Either_Right(xc)
                elif True:
                    d_975_newV_ = (_this).UpdateValues(a, wpre0, xc, xu, _dafny.SeqWithoutIsStrInference([]), _dafny.Set({}), 0)
                    in132_ = _this
                    in133_ = a
                    in134_ = wpre0
                    in135_ = (d_975_newV_)[1]
                    in136_ = (d_975_newV_)[0]
                    in137_ = (maxIter) - (1)
                    _this = in132_
                    
                    a = in133_
                    wpre0 = in134_
                    xu = in135_
                    xc = in136_
                    maxIter = in137_
                    raise _dafny.TailCall()
                break

    def UpdateValues(self, a, wpre0, xc, xu, newxc, newxu, index):
        _this = self
        while True:
            with _dafny.label():
                pat_let_tv8_ = a
                pat_let_tv9_ = index
                pat_let_tv10_ = xc
                pat_let_tv11_ = wpre0
                pat_let_tv12_ = index
                pat_let_tv13_ = a
                pat_let_tv14_ = index
                pat_let_tv15_ = xc
                pat_let_tv16_ = index
                if (len(xc)) == (index):
                    return (newxc, newxu)
                elif True:
                    def iife30_(_pat_let14_0):
                        def iife31_(d_977_seg_):
                            def lambda50_(d_978_xc_):
                                def lambda51_(d_979_i_):
                                    return (d_978_xc_)[d_979_i_]

                                return lambda51_

                            def iife32_(_pat_let15_0):
                                def iife33_(d_980_succWPre_):
                                    def iife34_(_pat_let16_0):
                                        def iife35_(d_981_m_):
                                            def iife36_(_pat_let17_0):
                                                def iife37_(d_982_d_):
                                                    return (d_982_d_, (MiscTypes.default__.SeqToSet((pat_let_tv13_).PredNat(pat_let_tv14_)) if (d_982_d_) > ((pat_let_tv15_)[pat_let_tv16_]) else _dafny.Set({})))
                                                return iife37_(_pat_let17_0)
                                            return iife36_((d_977_seg_).FastWeakestPreOperands(d_981_m_, (pat_let_tv11_)[pat_let_tv12_]))
                                        return iife35_(_pat_let16_0)
                                    return iife34_(EVMObj.MaxNatSeq(d_980_succWPre_))
                                return iife33_(_pat_let15_0)
                            return iife32_(MiscTypes.default__.MapP((pat_let_tv8_).SuccNat(pat_let_tv9_), lambda50_(pat_let_tv10_)))
                        return iife31_(_pat_let14_0)
                    d_976_n_ = (iife30_(((_this).xs)[(((a).states)[index]).segNum]) if (index) in (xu) else ((xc)[index], _dafny.Set({})))
                    in138_ = _this
                    in139_ = a
                    in140_ = wpre0
                    in141_ = xc
                    in142_ = xu
                    in143_ = (newxc) + (_dafny.SeqWithoutIsStrInference([(d_976_n_)[0]]))
                    in144_ = (newxu) | ((d_976_n_)[1])
                    in145_ = (index) + (1)
                    _this = in138_
                    
                    a = in139_
                    wpre0 = in140_
                    xc = in141_
                    xu = in142_
                    newxc = in143_
                    newxu = in144_
                    index = in145_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def MaxNat(a, b):
        if (a) > (b):
            return a
        elif True:
            return b

    @staticmethod
    def MaxNatSeq(xs):
        if (len(xs)) == (0):
            return 0
        elif True:
            return EVMObj.MaxNat((xs)[0], EVMObj.MaxNatSeq(_dafny.SeqWithoutIsStrInference((xs)[1::])))

    def ComputeWPreOperands(self, a):
        def lambda52_(d_985_a_):
            def lambda53_(d_986_i_):
                return (((self).xs)[(((d_985_a_).states)[d_986_i_]).segNum]).WeakestPreOperands((((self).xs)[(((d_985_a_).states)[d_986_i_]).segNum]).Ins(), 0)

            return lambda53_

        d_983_wpre0_ = MiscTypes.default__.MapP(_dafny.SeqWithoutIsStrInference([d_984_i_ for d_984_i_ in range(len((a).states))]), lambda52_(a))
        def iife38_():
            coll3_ = _dafny.Set()
            compr_3_: int
            for compr_3_ in _dafny.IntegerRange(0, len((a).states)):
                d_987_z_: int = compr_3_
                if ((0) <= (d_987_z_)) and ((d_987_z_) < (len((a).states))):
                    coll3_ = coll3_.union(_dafny.Set([d_987_z_]))
            return _dafny.Set(coll3_)
        return (self).Fix(a, d_983_wpre0_, iife38_()
        , d_983_wpre0_, (len((a).states)) + (1))

    def HasNoErrorState(self, a):
        def lambda54_(forall_var_10_):
            d_988_s_: CFGState.GState = forall_var_10_
            return not ((d_988_s_) in ((a).states)) or ((d_988_s_).is_EGState)

        return _dafny.quantifier(((a).states).UniqueElements, True, lambda54_)

    def PrintByteCodeInfo(self):
        d_989_listIns_: _dafny.Seq
        def lambda55_(d_990_s_):
            return (d_990_s_).Ins()

        d_989_listIns_ = MiscTypes.default__.Flatten(MiscTypes.default__.Map((self).xs, lambda55_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bytecode Size: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of((self).Size((self).xs)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " Bytes\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Number of instructions: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len(d_989_listIns_)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Arithmetic opcodes: "))).VerbatimString(False))
        def lambda56_(d_991_i_):
            return ((d_991_i_).op).is_ArithOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda56_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Comparison opcodes: "))).VerbatimString(False))
        def lambda57_(d_992_i_):
            return ((d_992_i_).op).is_CompOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda57_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise opcodes: "))).VerbatimString(False))
        def lambda58_(d_993_i_):
            return ((d_993_i_).op).is_BitwiseOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda58_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Keccak opcodes: "))).VerbatimString(False))
        def lambda59_(d_994_i_):
            return ((d_994_i_).op).is_KeccakOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda59_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Environmental opcodes: "))).VerbatimString(False))
        def lambda60_(d_995_i_):
            return ((d_995_i_).op).is_EnvOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda60_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage opcodes: "))).VerbatimString(False))
        def lambda61_(d_996_i_):
            return ((d_996_i_).op).is_StorageOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda61_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Memory opcodes: "))).VerbatimString(False))
        def lambda62_(d_997_i_):
            return ((d_997_i_).op).is_MemOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda62_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack opcodes: "))).VerbatimString(False))
        def lambda63_(d_998_i_):
            return ((d_998_i_).op).is_StackOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda63_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump opcodes: "))).VerbatimString(False))
        def lambda64_(d_999_i_):
            return ((d_999_i_).op).is_JumpOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda64_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Log opcodes: "))).VerbatimString(False))
        def lambda65_(d_1000_i_):
            return ((d_1000_i_).op).is_LogOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda65_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Revert/stop opcodes: "))).VerbatimString(False))
        def lambda66_(d_1001_i_):
            return (((d_1001_i_).op).is_SysOp) and (((d_1001_i_).op).IsRevertStop())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda66_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Return opcodes: "))).VerbatimString(False))
        def lambda67_(d_1002_i_):
            return (((d_1002_i_).op).is_SysOp) and (((d_1002_i_).op).IsReturn())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda67_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Invalid opcodes: "))).VerbatimString(False))
        def lambda68_(d_1003_i_):
            return (((d_1003_i_).op).is_SysOp) and (((d_1003_i_).op).IsInvalid())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda68_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Other Systems opcodes: "))).VerbatimString(False))
        def lambda69_(d_1004_i_):
            return (((((d_1004_i_).op).is_SysOp) and (not(((d_1004_i_).op).IsInvalid()))) and (not(((d_1004_i_).op).IsRevertStop()))) and (not(((d_1004_i_).op).IsReturn()))

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_989_listIns_, lambda69_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def PrintSegmentInfo(self):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Total number of segments: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len((self).xs)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of JUMP segments: "))).VerbatimString(False))
        def lambda70_(d_1005_s_):
            return (d_1005_s_).is_JUMPSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda70_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of JUMPI segments: "))).VerbatimString(False))
        def lambda71_(d_1006_s_):
            return (d_1006_s_).is_JUMPISeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda71_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of RETURN segments: "))).VerbatimString(False))
        def lambda72_(d_1007_s_):
            return (d_1007_s_).is_RETURNSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda72_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of STOP segments: "))).VerbatimString(False))
        def lambda73_(d_1008_s_):
            return (d_1008_s_).is_STOPSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda73_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of CONT segments: "))).VerbatimString(False))
        def lambda74_(d_1009_s_):
            return (d_1009_s_).is_CONTSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda74_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of INVALID segments: "))).VerbatimString(False))
        def lambda75_(d_1010_s_):
            return (d_1010_s_).is_INVALIDSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda75_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))


class EVMObj_EVMObj(EVMObj, NamedTuple('EVMObj', [('xs', Any), ('jumpDests', Any), ('PCToSegMap', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMObject.EVMObj.EVMObj({_dafny.string_of(self.xs)}, {_dafny.string_of(self.jumpDests)}, {_dafny.string_of(self.PCToSegMap)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, EVMObj_EVMObj) and self.xs == __o.xs and self.jumpDests == __o.jumpDests and self.PCToSegMap == __o.PCToSegMap
    def __hash__(self) -> int:
        return super().__hash__()

