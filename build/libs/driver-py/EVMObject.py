import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import MiscTypes as MiscTypes
import Int as Int
import EVMConstants as EVMConstants
import EVMOpcodes as EVMOpcodes
import OpcodeDecoder as OpcodeDecoder
import Hex as Hex
import StackElement as StackElement
import WeakPre as WeakPre
import State as State
import EVMToolTips as EVMToolTips
import Instructions as Instructions
import BinaryDecoder as BinaryDecoder
import LinSegments as LinSegments
import Splitter as Splitter
import SegBuilder as SegBuilder
import CFGState as CFGState
import ProofObject as ProofObject
import PrettyIns as PrettyIns
import PrettyPrinters as PrettyPrinters
import Automata as Automata
import SeqOfSets as SeqOfSets
import PartitionMod as PartitionMod
import GStateMinimiser as GStateMinimiser
import Statistics as Statistics
import HTML as HTML

# Module: EVMObject

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def CollectJumpDests(xs):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in0_
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
                    in0_ = xs
                    in1_ = (m).set(((xs)[index]).StartAddress(), index)
                    in2_ = (index) + (1)
                    xs = in0_
                    m = in1_
                    index = in2_
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
    def _Is(source__):
        d_0_xs_: _dafny.Seq = source__
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                d_2_i_k_: int = forall_var_1_
                return not ((((0) <= (d_1_i_)) and ((d_1_i_) < (d_2_i_k_))) and ((d_2_i_k_) < (len(d_0_xs_)))) or ((((d_0_xs_)[d_1_i_]).StartAddress()) < (((d_0_xs_)[d_2_i_k_]).StartAddress()))

            d_1_i_: int = forall_var_0_
            return _dafny.quantifier(_dafny.IntegerRange((d_1_i_) + (1), len(d_0_xs_)), True, lambda1_)

        return _dafny.quantifier(_dafny.IntegerRange(0, len(d_0_xs_)), True, lambda0_)

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

    def StackEffect(self, i):
        return (((self).xs)[i]).StackEffect()

    def CapEffect(self, i):
        return (((self).xs)[i]).NetCapEffect()

    def WpOp(self, i):
        return (((self).xs)[i]).WeakestPreOperands((((self).xs)[i]).Ins(), 0)

    def IsJump(self, i):
        return (((self).xs)[i]).IsJump()

    def WpCap(self, i):
        return (((self).xs)[i]).WeakestPreCapacity(0)

    def Size(self, ls):
        d_0___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (len(ls)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (((ls)[0]).Size(((ls)[0]).Ins()))
                    in0_ = _this
                    in1_ = _dafny.SeqWithoutIsStrInference((ls)[1::])
                    _this = in0_
                    
                    ls = in1_
                    raise _dafny.TailCall()
                break

    def NextG(self, s):
        source0_ = s
        if True:
            if source0_.is_ErrorGState:
                return _dafny.SeqWithoutIsStrInference([])
        if True:
            d_0_segNum_ = source0_.segNum
            d_1_st_ = source0_.st
            d_2_srcSeg_ = ((self).xs)[d_0_segNum_]
            d_3_src_ = State.AState_EState((d_2_srcSeg_).StartAddress(), d_1_st_)
            d_4_successors_ = _dafny.SeqWithoutIsStrInference([(d_2_srcSeg_).Run(d_3_src_, d_5_i_, (self).jumpDests) for d_5_i_ in range((d_2_srcSeg_).NumberOfExits())])
            def lambda0_(d_7_s_k_):
                def lambda1_():
                    source1_ = d_7_s_k_
                    if True:
                        if source1_.is_Error:
                            d_8_msg_ = source1_.msg
                            return CFGState.GState_ErrorGState(d_8_msg_)
                    if True:
                        d_9_pc_ = source1_.pc
                        d_10_st_ = source1_.stack
                        if (d_9_pc_) in ((self).PCToSegMap):
                            return CFGState.GState_EGState(((self).PCToSegMap)[d_9_pc_], (d_7_s_k_).stack)
                        elif True:
                            return CFGState.GState_ErrorGState(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "NextG:  "))) + (Int.default__.NatToString(d_9_pc_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " not defined"))))

                return lambda1_()

            d_6_succGStates_ = MiscTypes.default__.Map(d_4_successors_, lambda0_)
            return d_6_succGStates_

    def RunAll(self, exits, s):
        _this = self
        while True:
            with _dafny.label():
                if (len(exits)) == (0):
                    return s
                elif ((s).pc) in ((_this).PCToSegMap):
                    d_0_seg_ = ((_this).PCToSegMap)[(s).pc]
                    if ((((_this).xs)[d_0_seg_]).NumberOfExits()) > ((exits)[0]):
                        d_1_s_k_ = (((_this).xs)[d_0_seg_]).Run(s, (exits)[0], (_this).jumpDests)
                        if (d_1_s_k_).is_EState:
                            in0_ = _this
                            in1_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                            in2_ = d_1_s_k_
                            _this = in0_
                            
                            exits = in1_
                            s = in2_
                            raise _dafny.TailCall()
                        elif True:
                            return State.AState_Error(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Successor state of "))) + ((s).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " is not an EState"))))
                    elif True:
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit does not exist")))
                elif True:
                    return State.AState_Error((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found for state "))) + ((s).ToString()))
                break

    def PreservesCond(self, c, exits, initpc):
        pat_let_tv0_ = initpc
        def iife0_(_pat_let10_0):
            def iife1_(d_1_dt__update__tmp_h0_):
                def iife2_(_pat_let11_0):
                    def iife3_(d_2_dt__update_hpc_h0_):
                        return State.AState_EState(d_2_dt__update_hpc_h0_, (d_1_dt__update__tmp_h0_).stack)
                    return iife3_(_pat_let11_0)
                return iife2_(pat_let_tv0_)
            return iife1_(_pat_let10_0)
        d_0_initState_ = iife0_(State.default__.BuildInitState(c, 0))
        d_3_endState_ = (self).RunAll(exits, d_0_initState_)
        if (d_3_endState_).is_EState:
            return (d_3_endState_).Sat(c)
        elif True:
            return False

    def SafeLoopFound(self, i, pStates, pExits):
        _this = self
        while True:
            with _dafny.label():
                source0_ = (_this).FindFirstNodeWithSegIndex(i, pStates, 0)
                if True:
                    if source0_.is_Some:
                        d_0_index_ = source0_.v
                        d_1_pathFromIndex_ = _dafny.SeqWithoutIsStrInference((pStates)[d_0_index_::])
                        d_2_exitsFromIndex_ = _dafny.SeqWithoutIsStrInference((pExits)[d_0_index_::])
                        d_3_segmentsOnPathFromIndex_ = _dafny.SeqWithoutIsStrInference([((d_1_pathFromIndex_)[d_4_i_]).segNum for d_4_i_ in range(len(d_1_pathFromIndex_))])
                        d_5_tgtCond_ = (((_this).xs)[(MiscTypes.default__.Last(pStates)).segNum]).LeadsTo((((_this).xs)[i]).StartAddress(), MiscTypes.default__.Last(pExits))
                        d_6_w1_ = LinSegments.default__.WPreSeqSegs(d_3_segmentsOnPathFromIndex_, d_2_exitsFromIndex_, (d_5_tgtCond_).And(WeakPre.default__.StackToCond(((pStates)[d_0_index_]).st)), (_this).xs, (((_this).xs)[i]).StartAddress())
                        if (d_6_w1_).is_StTrue:
                            return MiscTypes.Option_Some(d_0_index_)
                        elif (d_6_w1_).is_StFalse:
                            return MiscTypes.Option_None()
                        elif (_this).PreservesCond(d_6_w1_, d_2_exitsFromIndex_, (((_this).xs)[i]).StartAddress()):
                            return MiscTypes.Option_Some(d_0_index_)
                        elif (0) < (len(d_1_pathFromIndex_)):
                            in0_ = _this
                            in1_ = i
                            in2_ = _dafny.SeqWithoutIsStrInference((d_1_pathFromIndex_)[1::])
                            in3_ = _dafny.SeqWithoutIsStrInference((d_2_exitsFromIndex_)[1::])
                            _this = in0_
                            
                            i = in1_
                            pStates = in2_
                            pExits = in3_
                            raise _dafny.TailCall()
                        elif True:
                            return MiscTypes.Option_None()
                if True:
                    return MiscTypes.Option_None()
                break

    def FindFirstNodeWithSegIndex(self, i, gs, index):
        _this = self
        while True:
            with _dafny.label():
                if (len(gs)) == (index):
                    return MiscTypes.Option_None()
                elif True:
                    source0_ = (gs)[index]
                    if True:
                        if source0_.is_EGState:
                            d_0_i_k_ = source0_.segNum
                            d_1_st_ = source0_.st
                            if (d_0_i_k_) == (i):
                                return MiscTypes.Option_Some(index)
                            elif True:
                                in0_ = _this
                                in1_ = i
                                in2_ = gs
                                in3_ = (index) + (1)
                                _this = in0_
                                
                                i = in1_
                                gs = in2_
                                index = in3_
                                raise _dafny.TailCall()
                    if True:
                        d_2_m_ = source0_.msg
                        return MiscTypes.Option_None()
                break

    def DFS(self, p, a, maxDepth, debugInfo, stats):
        a_k: Automata.Auto = Automata.ValidAuto.default()
        stats_k: Statistics.Stats = Statistics.Stats.default()()
        d_0_lastOnPath_: CFGState.GState
        d_0_lastOnPath_ = MiscTypes.default__.Last((p).states)
        if ((maxDepth) == (0)) or ((d_0_lastOnPath_).is_ErrorGState):
            d_1_stats_k_: Statistics.Stats
            if (maxDepth) == (0):
                d_1_stats_k_ = (stats).SetMaxDepth()
            elif True:
                d_1_stats_k_ = stats
            rhs0_ = a
            rhs1_ = d_1_stats_k_
            a_k = rhs0_
            stats_k = rhs1_
            return a_k, stats_k
        elif True:
            a_k = a
            stats_k = stats
            hi0_ = len((self).NextG(d_0_lastOnPath_))
            for d_2_i_ in range(0, hi0_):
                d_3_i__th__succ_: CFGState.GState
                d_3_i__th__succ_ = ((self).NextG(d_0_lastOnPath_))[d_2_i_]
                if (d_3_i__th__succ_).is_ErrorGState:
                    rhs2_ = (a_k).AddEdge(d_0_lastOnPath_, d_3_i__th__succ_)
                    rhs3_ = (stats_k).IncError()
                    a_k = rhs2_
                    stats_k = rhs3_
                elif (d_3_i__th__succ_) in ((a_k).indexOf):
                    rhs4_ = (a_k).AddEdge(d_0_lastOnPath_, ((a_k).states)[((a_k).indexOf)[d_3_i__th__succ_]])
                    rhs5_ = (stats_k).IncVisited()
                    a_k = rhs4_
                    stats_k = rhs5_
                elif not((((self).xs)[(d_0_lastOnPath_).segNum]).IsJump()):
                    d_4_j_: Automata.Auto
                    d_4_j_ = (a_k).AddEdge(d_0_lastOnPath_, d_3_i__th__succ_)
                    d_5_p_k_: Path
                    d_5_p_k_ = Path_Path(((p).states) + (_dafny.SeqWithoutIsStrInference([d_3_i__th__succ_])), ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_2_i_])))
                    out0_: Automata.Auto
                    out1_: Statistics.Stats
                    out0_, out1_ = (self).DFS(d_5_p_k_, d_4_j_, (maxDepth) - (1), debugInfo, stats_k)
                    a_k = out0_
                    stats_k = out1_
                elif True:
                    source0_ = (self).SafeLoopFound((d_3_i__th__succ_).segNum, (p).states, ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_2_i_])))
                    with _dafny.label("match0"):
                        if True:
                            if source0_.is_Some:
                                d_6_index_ = source0_.v
                                rhs6_ = (a_k).AddEdge(d_0_lastOnPath_, ((p).states)[d_6_index_])
                                rhs7_ = (stats_k).IncWpre()
                                a_k = rhs6_
                                stats_k = rhs7_
                                raise _dafny.Break("match0")
                        if True:
                            out2_: Automata.Auto
                            out3_: Statistics.Stats
                            out2_, out3_ = (self).DFS(Path_Path(((p).states) + (_dafny.SeqWithoutIsStrInference([d_3_i__th__succ_])), ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_2_i_]))), (a_k).AddEdge(d_0_lastOnPath_, d_3_i__th__succ_), (maxDepth) - (1), debugInfo, stats_k)
                            a_k = out2_
                            stats_k = out3_
                        pass
        return a_k, stats_k

    def BuildCFG(self, maxDepth, minimise):
        a: Automata.Auto = Automata.ValidAuto.default()
        stats: Statistics.Stats = Statistics.Stats.default()()
        d_0_a1_: Automata.Auto
        d_1_s1_: Statistics.Stats
        out0_: Automata.Auto
        out1_: Statistics.Stats
        out0_, out1_ = (self).DFS(Path_Path(_dafny.SeqWithoutIsStrInference([CFGState.default__.DEFAULT__GSTATE]), _dafny.SeqWithoutIsStrInference([])), (Automata.Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({}))).AddState(CFGState.default__.DEFAULT__GSTATE), maxDepth, True, Statistics.Stats_Stats(False, 0, 0, 0, (0, 0)))
        d_0_a1_ = out0_
        d_1_s1_ = out1_
        if (not(minimise)) or (((d_0_a1_).SSize()) == (0)):
            rhs0_ = d_0_a1_
            rhs1_ = d_1_s1_
            a = rhs0_
            stats = rhs1_
            return a, stats
        elif True:
            d_2_p1_: PartitionMod.Partition
            d_2_p1_ = PartitionMod.default__.MakeInit((d_0_a1_).SSize())
            d_3_e_: Callable
            def lambda0_(d_4_a1_):
                def lambda1_(d_5_x_, d_6_y_):
                    def lambda2_():
                        source0_ = (((d_4_a1_).states)[d_5_x_], ((d_4_a1_).states)[d_6_y_])
                        if True:
                            d_00_ = source0_[0]
                            if d_00_.is_EGState:
                                d_7_s1_ = d_00_.segNum
                                d_10_ = source0_[1]
                                if d_10_.is_EGState:
                                    d_8_s2_ = d_10_.segNum
                                    return (d_7_s1_) == (d_8_s2_)
                        if True:
                            return False

                    return (True if (d_5_x_) == (d_6_y_) else lambda2_())

                return lambda1_

            d_3_e_ = lambda0_(d_0_a1_)
            d_9_p2_: PartitionMod.Partition
            d_9_p2_ = (d_2_p1_).ComputeFinest(d_3_e_)
            d_10_vp_: GStateMinimiser.Pair
            d_10_vp_ = GStateMinimiser.Pair_Pair(d_0_a1_, d_9_p2_)
            d_11_a2_: Automata.Auto
            d_11_a2_ = (d_10_vp_).Minimise()
            pat_let_tv0_ = d_0_a1_
            pat_let_tv1_ = d_0_a1_
            def iife0_(_pat_let12_0):
                def iife1_(d_12_dt__update__tmp_h0_):
                    def iife2_(_pat_let13_0):
                        def iife3_(d_13_dt__update_hnonMinimisedSize_h0_):
                            return Statistics.Stats_Stats((d_12_dt__update__tmp_h0_).maxDepthReached, (d_12_dt__update__tmp_h0_).visitedStates, (d_12_dt__update__tmp_h0_).wPreInvSuccess, (d_12_dt__update__tmp_h0_).errorState, d_13_dt__update_hnonMinimisedSize_h0_)
                        return iife3_(_pat_let13_0)
                    return iife2_(((pat_let_tv0_).SSize(), (pat_let_tv1_).TSize(0)))
                return iife1_(_pat_let12_0)
            rhs2_ = d_11_a2_
            rhs3_ = iife0_(d_1_s1_)
            a = rhs2_
            stats = rhs3_
            return a, stats
        return a, stats

    def ToHTML(self, a, withTable, minStackSizeForState, index):
        if (a).is_ErrorGState:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"))
        elif withTable:
            return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<"))) + (HTML.default__.DOTSegTable(((self).xs)[(a).segNum], a, minStackSizeForState, index))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))
        elif True:
            return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<"))) + ((HTML.default__.DOTSeg(((self).xs)[(a).segNum], (a).segNum, minStackSizeForState, index))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))

    def DotLabel(self, s, exit):
        d_0_lab_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")) if (s).is_ErrorGState else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Jump\",style=dashed")) if ((((self).xs)[(s).segNum]).IsJump()) and ((exit) == (((((self).xs)[(s).segNum]).NumberOfExits()) - (1))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Next\""))) if ((s).is_EGState) and ((exit) < ((((self).xs)[(s).segNum]).NumberOfExits())) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error Number of exits"))))
        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ["))) + (d_0_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))

    def Fix(self, a, wpre0, xu, xc, maxIter):
        _this = self
        while True:
            with _dafny.label():
                if (xu) == (_dafny.Set({})):
                    return MiscTypes.Either_Left(xc)
                elif (maxIter) == (0):
                    return MiscTypes.Either_Right(xc)
                elif True:
                    d_0_newV_ = (_this).UpdateValues(a, wpre0, xc, xu, _dafny.SeqWithoutIsStrInference([]), _dafny.Set({}), 0)
                    in0_ = _this
                    in1_ = a
                    in2_ = wpre0
                    in3_ = (d_0_newV_)[1]
                    in4_ = (d_0_newV_)[0]
                    in5_ = (maxIter) - (1)
                    _this = in0_
                    
                    a = in1_
                    wpre0 = in2_
                    xu = in3_
                    xc = in4_
                    maxIter = in5_
                    raise _dafny.TailCall()
                break

    def UpdateValues(self, a, wpre0, xc, xu, newxc, newxu, index):
        _this = self
        while True:
            with _dafny.label():
                pat_let_tv0_ = a
                pat_let_tv1_ = index
                pat_let_tv2_ = xc
                pat_let_tv3_ = a
                pat_let_tv4_ = index
                pat_let_tv5_ = wpre0
                pat_let_tv6_ = index
                pat_let_tv7_ = a
                pat_let_tv8_ = index
                pat_let_tv9_ = xc
                pat_let_tv10_ = index
                if (len(xc)) == (index):
                    return (newxc, newxu)
                elif True:
                    def iife0_(_pat_let14_0):
                        def iife1_(d_1_seg_):
                            def iife2_(_pat_let15_0):
                                def iife3_(d_3_succWPre_):
                                    def iife4_(_pat_let16_0):
                                        def iife5_(d_4_m_):
                                            def iife6_(_pat_let17_0):
                                                def iife7_(d_5_d_):
                                                    return (d_5_d_, (MiscTypes.default__.SeqToSet((pat_let_tv7_).PredNat(pat_let_tv8_)) if (d_5_d_) > ((pat_let_tv9_)[pat_let_tv10_]) else _dafny.Set({})))
                                                return iife7_(_pat_let17_0)
                                            return iife6_((d_1_seg_).FastWeakestPreOperands(d_4_m_, (pat_let_tv5_)[pat_let_tv6_]))
                                        return iife5_(_pat_let16_0)
                                    return iife4_(EVMObj.MaxNatSeq(d_3_succWPre_))
                                return iife3_(_pat_let15_0)
                            return iife2_(_dafny.SeqWithoutIsStrInference([(pat_let_tv2_)[((pat_let_tv3_).SuccNat(pat_let_tv4_))[d_2_i_]] for d_2_i_ in range(len((pat_let_tv0_).SuccNat(pat_let_tv1_)))]))
                        return iife1_(_pat_let14_0)
                    d_0_n_ = (iife0_(((_this).xs)[(((a).states)[index]).segNum]) if (index) in (xu) else ((xc)[index], _dafny.Set({})))
                    in0_ = _this
                    in1_ = a
                    in2_ = wpre0
                    in3_ = xc
                    in4_ = xu
                    in5_ = (newxc) + (_dafny.SeqWithoutIsStrInference([(d_0_n_)[0]]))
                    in6_ = (newxu) | ((d_0_n_)[1])
                    in7_ = (index) + (1)
                    _this = in0_
                    
                    a = in1_
                    wpre0 = in2_
                    xc = in3_
                    xu = in4_
                    newxc = in5_
                    newxu = in6_
                    index = in7_
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
        def lambda0_(d_2_a_):
            def lambda1_(d_3_i_):
                return (((self).xs)[(((d_2_a_).states)[d_3_i_]).segNum]).WeakestPreOperands((((self).xs)[(((d_2_a_).states)[d_3_i_]).segNum]).Ins(), 0)

            return lambda1_

        d_0_wpre0_ = MiscTypes.default__.MapP(_dafny.SeqWithoutIsStrInference([d_1_i_ for d_1_i_ in range(len((a).states))]), lambda0_(a))
        def iife0_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, len((a).states)):
                d_4_z_: int = compr_0_
                if ((0) <= (d_4_z_)) and ((d_4_z_) < (len((a).states))):
                    coll0_ = coll0_.union(_dafny.Set([d_4_z_]))
            return _dafny.Set(coll0_)
        return (self).Fix(a, d_0_wpre0_, iife0_()
        , d_0_wpre0_, (len((a).states)) + (1))

    def HasNoErrorState(self, a):
        def lambda0_(forall_var_0_):
            d_0_s_: CFGState.GState = forall_var_0_
            return not ((d_0_s_) in ((a).states)) or ((d_0_s_).is_EGState)

        return _dafny.quantifier(((a).states).UniqueElements, True, lambda0_)

    def PrintByteCodeInfo(self):
        d_0_listIns_: _dafny.Seq
        def lambda0_(d_1_s_):
            return (d_1_s_).Ins()

        d_0_listIns_ = MiscTypes.default__.Flatten(MiscTypes.default__.Map((self).xs, lambda0_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bytecode Size: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of((self).Size((self).xs)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " Bytes\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Number of instructions: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len(d_0_listIns_)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Arithmetic opcodes: "))).VerbatimString(False))
        def lambda1_(d_2_i_):
            return ((d_2_i_).op).is_ArithOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda1_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Comparison opcodes: "))).VerbatimString(False))
        def lambda2_(d_3_i_):
            return ((d_3_i_).op).is_CompOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda2_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise opcodes: "))).VerbatimString(False))
        def lambda3_(d_4_i_):
            return ((d_4_i_).op).is_BitwiseOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda3_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Keccak opcodes: "))).VerbatimString(False))
        def lambda4_(d_5_i_):
            return ((d_5_i_).op).is_KeccakOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda4_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Environmental opcodes: "))).VerbatimString(False))
        def lambda5_(d_6_i_):
            return ((d_6_i_).op).is_EnvOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda5_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage opcodes: "))).VerbatimString(False))
        def lambda6_(d_7_i_):
            return ((d_7_i_).op).is_StorageOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda6_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Memory opcodes: "))).VerbatimString(False))
        def lambda7_(d_8_i_):
            return ((d_8_i_).op).is_MemOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda7_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack opcodes: "))).VerbatimString(False))
        def lambda8_(d_9_i_):
            return ((d_9_i_).op).is_StackOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda8_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump opcodes: "))).VerbatimString(False))
        def lambda9_(d_10_i_):
            return ((d_10_i_).op).is_JumpOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda9_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Log opcodes: "))).VerbatimString(False))
        def lambda10_(d_11_i_):
            return ((d_11_i_).op).is_LogOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda10_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Revert/stop opcodes: "))).VerbatimString(False))
        def lambda11_(d_12_i_):
            return (((d_12_i_).op).is_SysOp) and (((d_12_i_).op).IsRevertStop())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda11_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Return opcodes: "))).VerbatimString(False))
        def lambda12_(d_13_i_):
            return (((d_13_i_).op).is_SysOp) and (((d_13_i_).op).IsReturn())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda12_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Invalid opcodes: "))).VerbatimString(False))
        def lambda13_(d_14_i_):
            return (((d_14_i_).op).is_SysOp) and (((d_14_i_).op).IsInvalid())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda13_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Other Systems opcodes: "))).VerbatimString(False))
        def lambda14_(d_15_i_):
            return (((((d_15_i_).op).is_SysOp) and (not(((d_15_i_).op).IsInvalid()))) and (not(((d_15_i_).op).IsRevertStop()))) and (not(((d_15_i_).op).IsReturn()))

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_0_listIns_, lambda14_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def PrintSegmentInfo(self):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Total number of segments: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len((self).xs)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of JUMP segments: "))).VerbatimString(False))
        def lambda0_(d_0_s_):
            return (d_0_s_).is_JUMPSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda0_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of JUMPI segments: "))).VerbatimString(False))
        def lambda1_(d_1_s_):
            return (d_1_s_).is_JUMPISeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda1_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of RETURN segments: "))).VerbatimString(False))
        def lambda2_(d_2_s_):
            return (d_2_s_).is_RETURNSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda2_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of STOP segments: "))).VerbatimString(False))
        def lambda3_(d_3_s_):
            return (d_3_s_).is_STOPSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda3_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of CONT segments: "))).VerbatimString(False))
        def lambda4_(d_4_s_):
            return (d_4_s_).is_CONTSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda4_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of INVALID segments: "))).VerbatimString(False))
        def lambda5_(d_5_s_):
            return (d_5_s_).is_INVALIDSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda5_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))


class EVMObj_EVMObj(EVMObj, NamedTuple('EVMObj', [('xs', Any), ('jumpDests', Any), ('PCToSegMap', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMObject.EVMObj.EVMObj({_dafny.string_of(self.xs)}, {_dafny.string_of(self.jumpDests)}, {_dafny.string_of(self.PCToSegMap)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, EVMObj_EVMObj) and self.xs == __o.xs and self.jumpDests == __o.jumpDests and self.PCToSegMap == __o.PCToSegMap
    def __hash__(self) -> int:
        return super().__hash__()

