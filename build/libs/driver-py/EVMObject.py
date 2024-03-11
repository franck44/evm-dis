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
import CFGState
import ProofObject
import PrettyIns
import PrettyPrinters
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
        d_928___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_928___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_928___accumulator_ = (d_928___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in130_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in130_
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
                    in131_ = xs
                    in132_ = (m).set(((xs)[index]).StartAddress(), index)
                    in133_ = (index) + (1)
                    xs = in131_
                    m = in132_
                    index = in133_
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
        d_929___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (len(ls)) == (0):
                    return (0) + (d_929___accumulator_)
                elif True:
                    d_929___accumulator_ = (d_929___accumulator_) + (((ls)[0]).Size(((ls)[0]).Ins()))
                    in134_ = _this
                    in135_ = _dafny.SeqWithoutIsStrInference((ls)[1::])
                    _this = in134_
                    
                    ls = in135_
                    raise _dafny.TailCall()
                break

    def NextG(self, s):
        source62_ = s
        if source62_.is_EGState:
            d_930___mcc_h0_ = source62_.segNum
            d_931___mcc_h1_ = source62_.st
            d_932_st_ = d_931___mcc_h1_
            d_933_segNum_ = d_930___mcc_h0_
            d_934_srcSeg_ = ((self).xs)[d_933_segNum_]
            d_935_src_ = State.AState_EState((d_934_srcSeg_).StartAddress(), d_932_st_)
            d_936_successors_ = _dafny.SeqWithoutIsStrInference([(d_934_srcSeg_).Run(d_935_src_, d_937_i_, (self).jumpDests) for d_937_i_ in range((d_934_srcSeg_).NumberOfExits())])
            def lambda45_(d_939_s_k_):
                def lambda46_(source63_):
                    if source63_.is_EState:
                        d_940___mcc_h3_ = source63_.pc
                        d_941___mcc_h4_ = source63_.stack
                        d_942_st_ = d_941___mcc_h4_
                        d_943_pc_ = d_940___mcc_h3_
                        if (d_943_pc_) in ((self).PCToSegMap):
                            return CFGState.GState_EGState(((self).PCToSegMap)[d_943_pc_], (d_939_s_k_).stack)
                        elif True:
                            return CFGState.GState_ErrorGState(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "NextG:  "))) + (Int.default__.NatToString(d_943_pc_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " not defined"))))
                    elif True:
                        d_944___mcc_h5_ = source63_.msg
                        d_945_msg_ = d_944___mcc_h5_
                        return CFGState.GState_ErrorGState(d_945_msg_)

                return lambda46_(d_939_s_k_)

            d_938_succGStates_ = MiscTypes.default__.Map(d_936_successors_, lambda45_)
            return d_938_succGStates_
        elif True:
            d_946___mcc_h2_ = source62_.msg
            return _dafny.SeqWithoutIsStrInference([])

    def RunAll(self, exits, s):
        _this = self
        while True:
            with _dafny.label():
                if (len(exits)) == (0):
                    return s
                elif ((s).pc) in ((_this).PCToSegMap):
                    d_947_seg_ = ((_this).PCToSegMap)[(s).pc]
                    if ((((_this).xs)[d_947_seg_]).NumberOfExits()) > ((exits)[0]):
                        d_948_s_k_ = (((_this).xs)[d_947_seg_]).Run(s, (exits)[0], (_this).jumpDests)
                        if (d_948_s_k_).is_EState:
                            in136_ = _this
                            in137_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                            in138_ = d_948_s_k_
                            _this = in136_
                            
                            exits = in137_
                            s = in138_
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
            def iife23_(d_950_dt__update__tmp_h0_):
                def iife24_(_pat_let11_0):
                    def iife25_(d_951_dt__update_hpc_h0_):
                        return State.AState_EState(d_951_dt__update_hpc_h0_, (d_950_dt__update__tmp_h0_).stack)
                    return iife25_(_pat_let11_0)
                return iife24_(pat_let_tv5_)
            return iife23_(_pat_let10_0)
        d_949_initState_ = iife22_(State.default__.BuildInitState(c, 0))
        d_952_endState_ = (self).RunAll(exits, d_949_initState_)
        if (d_952_endState_).is_EState:
            return (d_952_endState_).Sat(c)
        elif True:
            return False

    def SafeLoopFound(self, i, pStates, pExits):
        _this = self
        while True:
            with _dafny.label():
                source64_ = (_this).FindFirstNodeWithSegIndex(i, pStates, 0)
                if source64_.is_None:
                    return MiscTypes.Option_None()
                elif True:
                    d_953___mcc_h0_ = source64_.v
                    d_954_index_ = d_953___mcc_h0_
                    d_955_pathFromIndex_ = _dafny.SeqWithoutIsStrInference((pStates)[d_954_index_::])
                    d_956_exitsFromIndex_ = _dafny.SeqWithoutIsStrInference((pExits)[d_954_index_::])
                    d_957_segmentsOnPathFromIndex_ = _dafny.SeqWithoutIsStrInference([((d_955_pathFromIndex_)[d_958_i_]).segNum for d_958_i_ in range(len(d_955_pathFromIndex_))])
                    d_959_tgtCond_ = (((_this).xs)[(MiscTypes.default__.Last(pStates)).segNum]).LeadsTo((((_this).xs)[i]).StartAddress(), MiscTypes.default__.Last(pExits))
                    d_960_w1_ = LinSegments.default__.WPreSeqSegs(d_957_segmentsOnPathFromIndex_, d_956_exitsFromIndex_, (d_959_tgtCond_).And(WeakPre.default__.StackToCond(((pStates)[d_954_index_]).st)), (_this).xs, (((_this).xs)[i]).StartAddress())
                    if (d_960_w1_).is_StTrue:
                        return MiscTypes.Option_Some(d_954_index_)
                    elif (d_960_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif (_this).PreservesCond(d_960_w1_, d_956_exitsFromIndex_, (((_this).xs)[i]).StartAddress()):
                        return MiscTypes.Option_Some(d_954_index_)
                    elif (0) < (len(d_955_pathFromIndex_)):
                        in139_ = _this
                        in140_ = i
                        in141_ = _dafny.SeqWithoutIsStrInference((d_955_pathFromIndex_)[1::])
                        in142_ = _dafny.SeqWithoutIsStrInference((d_956_exitsFromIndex_)[1::])
                        _this = in139_
                        
                        i = in140_
                        pStates = in141_
                        pExits = in142_
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
                    source65_ = (gs)[index]
                    if source65_.is_EGState:
                        d_961___mcc_h0_ = source65_.segNum
                        d_962___mcc_h1_ = source65_.st
                        d_963_st_ = d_962___mcc_h1_
                        d_964_i_k_ = d_961___mcc_h0_
                        if (d_964_i_k_) == (i):
                            return MiscTypes.Option_Some(index)
                        elif True:
                            in143_ = _this
                            in144_ = i
                            in145_ = gs
                            in146_ = (index) + (1)
                            _this = in143_
                            
                            i = in144_
                            gs = in145_
                            index = in146_
                            raise _dafny.TailCall()
                    elif True:
                        d_965___mcc_h2_ = source65_.msg
                        d_966_m_ = d_965___mcc_h2_
                        return MiscTypes.Option_None()
                break

    def DFS(self, p, a, maxDepth, debugInfo, stats):
        a_k: Automata.Auto = Automata.ValidAuto.default()
        stats_k: Statistics.Stats = Statistics.Stats.default()()
        d_967_lastOnPath_: CFGState.GState
        d_967_lastOnPath_ = MiscTypes.default__.Last((p).states)
        if ((maxDepth) == (0)) or ((d_967_lastOnPath_).is_ErrorGState):
            d_968_stats_k_: Statistics.Stats
            d_968_stats_k_ = ((stats).SetMaxDepth() if (maxDepth) == (0) else stats)
            rhs0_ = a
            rhs1_ = d_968_stats_k_
            a_k = rhs0_
            stats_k = rhs1_
            return a_k, stats_k
        elif True:
            a_k = a
            stats_k = stats
            hi4_ = len((self).NextG(d_967_lastOnPath_))
            for d_969_i_ in range(0, hi4_):
                d_970_i__th__succ_: CFGState.GState
                d_970_i__th__succ_ = ((self).NextG(d_967_lastOnPath_))[d_969_i_]
                if (d_970_i__th__succ_).is_ErrorGState:
                    rhs2_ = (a_k).AddEdge(d_967_lastOnPath_, d_970_i__th__succ_)
                    rhs3_ = (stats_k).IncError()
                    a_k = rhs2_
                    stats_k = rhs3_
                elif (d_970_i__th__succ_) in ((a_k).indexOf):
                    rhs4_ = (a_k).AddEdge(d_967_lastOnPath_, ((a_k).states)[((a_k).indexOf)[d_970_i__th__succ_]])
                    rhs5_ = (stats_k).IncVisited()
                    a_k = rhs4_
                    stats_k = rhs5_
                elif not((((self).xs)[(d_967_lastOnPath_).segNum]).IsJump()):
                    d_971_j_: Automata.Auto
                    d_971_j_ = (a_k).AddEdge(d_967_lastOnPath_, d_970_i__th__succ_)
                    d_972_p_k_: Path
                    d_972_p_k_ = Path_Path(((p).states) + (_dafny.SeqWithoutIsStrInference([d_970_i__th__succ_])), ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_969_i_])))
                    out0_: Automata.Auto
                    out1_: Statistics.Stats
                    out0_, out1_ = (self).DFS(d_972_p_k_, d_971_j_, (maxDepth) - (1), debugInfo, stats_k)
                    a_k = out0_
                    stats_k = out1_
                elif True:
                    source66_ = (self).SafeLoopFound((d_970_i__th__succ_).segNum, (p).states, ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_969_i_])))
                    if source66_.is_None:
                        out2_: Automata.Auto
                        out3_: Statistics.Stats
                        out2_, out3_ = (self).DFS(Path_Path(((p).states) + (_dafny.SeqWithoutIsStrInference([d_970_i__th__succ_])), ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_969_i_]))), (a_k).AddEdge(d_967_lastOnPath_, d_970_i__th__succ_), (maxDepth) - (1), debugInfo, stats_k)
                        a_k = out2_
                        stats_k = out3_
                    elif True:
                        d_973___mcc_h0_ = source66_.v
                        d_974_index_ = d_973___mcc_h0_
                        rhs6_ = (a_k).AddEdge(d_967_lastOnPath_, ((p).states)[d_974_index_])
                        rhs7_ = (stats_k).IncWpre()
                        a_k = rhs6_
                        stats_k = rhs7_
        return a_k, stats_k

    def BuildCFG(self, maxDepth, minimise):
        a: Automata.Auto = Automata.ValidAuto.default()
        stats: Statistics.Stats = Statistics.Stats.default()()
        d_975_a1_: Automata.Auto
        d_976_s1_: Statistics.Stats
        out4_: Automata.Auto
        out5_: Statistics.Stats
        out4_, out5_ = (self).DFS(Path_Path(_dafny.SeqWithoutIsStrInference([CFGState.default__.DEFAULT__GSTATE]), _dafny.SeqWithoutIsStrInference([])), (Automata.Auto_Auto(_dafny.Map({}), _dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({}))).AddState(CFGState.default__.DEFAULT__GSTATE), maxDepth, True, Statistics.Stats_Stats(False, 0, 0, 0, (0, 0)))
        d_975_a1_ = out4_
        d_976_s1_ = out5_
        if (not(minimise)) or (((d_975_a1_).SSize()) == (0)):
            rhs8_ = d_975_a1_
            rhs9_ = d_976_s1_
            a = rhs8_
            stats = rhs9_
            return a, stats
        elif True:
            d_977_p1_: PartitionMod.Partition
            d_977_p1_ = PartitionMod.default__.MakeInit((d_975_a1_).SSize())
            d_978_e_: Callable
            def lambda47_(d_979_a1_):
                def lambda48_(d_980_x_, d_981_y_):
                    def lambda49_(source67_):
                        d_982___mcc_h0_ = source67_[0]
                        d_983___mcc_h1_ = source67_[1]
                        source68_ = d_982___mcc_h0_
                        if source68_.is_EGState:
                            d_984___mcc_h2_ = source68_.segNum
                            d_985___mcc_h3_ = source68_.st
                            source69_ = d_983___mcc_h1_
                            if source69_.is_EGState:
                                d_986___mcc_h6_ = source69_.segNum
                                d_987___mcc_h7_ = source69_.st
                                d_988_s2_ = d_986___mcc_h6_
                                d_989_s1_ = d_984___mcc_h2_
                                return (d_989_s1_) == (d_988_s2_)
                            elif True:
                                d_990___mcc_h10_ = source69_.msg
                                return False
                        elif True:
                            d_991___mcc_h12_ = source68_.msg
                            return False

                    return (True if (d_980_x_) == (d_981_y_) else lambda49_((((d_979_a1_).states)[d_980_x_], ((d_979_a1_).states)[d_981_y_])))

                return lambda48_

            d_978_e_ = lambda47_(d_975_a1_)
            d_992_p2_: PartitionMod.Partition
            d_992_p2_ = (d_977_p1_).ComputeFinest(d_978_e_)
            d_993_vp_: GStateMinimiser.Pair
            d_993_vp_ = GStateMinimiser.Pair_Pair(d_975_a1_, d_992_p2_)
            d_994_a2_: Automata.Auto
            d_994_a2_ = (d_993_vp_).Minimise()
            pat_let_tv6_ = d_975_a1_
            pat_let_tv7_ = d_975_a1_
            def iife26_(_pat_let12_0):
                def iife27_(d_995_dt__update__tmp_h0_):
                    def iife28_(_pat_let13_0):
                        def iife29_(d_996_dt__update_hnonMinimisedSize_h0_):
                            return Statistics.Stats_Stats((d_995_dt__update__tmp_h0_).maxDepthReached, (d_995_dt__update__tmp_h0_).visitedStates, (d_995_dt__update__tmp_h0_).wPreInvSuccess, (d_995_dt__update__tmp_h0_).errorState, d_996_dt__update_hnonMinimisedSize_h0_)
                        return iife29_(_pat_let13_0)
                    return iife28_(((pat_let_tv6_).SSize(), (pat_let_tv7_).TSize(0)))
                return iife27_(_pat_let12_0)
            rhs10_ = d_994_a2_
            rhs11_ = iife26_(d_976_s1_)
            a = rhs10_
            stats = rhs11_
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
        d_997_lab_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")) if (s).is_ErrorGState else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Jump\",style=dashed")) if ((((self).xs)[(s).segNum]).IsJump()) and ((exit) == (((((self).xs)[(s).segNum]).NumberOfExits()) - (1))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Next\""))) if ((s).is_EGState) and ((exit) < ((((self).xs)[(s).segNum]).NumberOfExits())) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error Number of exits"))))
        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ["))) + (d_997_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))

    def Fix(self, a, wpre0, xu, xc, maxIter):
        _this = self
        while True:
            with _dafny.label():
                if (xu) == (_dafny.Set({})):
                    return MiscTypes.Either_Left(xc)
                elif (maxIter) == (0):
                    return MiscTypes.Either_Right(xc)
                elif True:
                    d_998_newV_ = (_this).UpdateValues(a, wpre0, xc, xu, _dafny.SeqWithoutIsStrInference([]), _dafny.Set({}), 0)
                    in147_ = _this
                    in148_ = a
                    in149_ = wpre0
                    in150_ = (d_998_newV_)[1]
                    in151_ = (d_998_newV_)[0]
                    in152_ = (maxIter) - (1)
                    _this = in147_
                    
                    a = in148_
                    wpre0 = in149_
                    xu = in150_
                    xc = in151_
                    maxIter = in152_
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
                        def iife31_(d_1000_seg_):
                            def lambda50_(d_1001_xc_):
                                def lambda51_(d_1002_i_):
                                    return (d_1001_xc_)[d_1002_i_]

                                return lambda51_

                            def iife32_(_pat_let15_0):
                                def iife33_(d_1003_succWPre_):
                                    def iife34_(_pat_let16_0):
                                        def iife35_(d_1004_m_):
                                            def iife36_(_pat_let17_0):
                                                def iife37_(d_1005_d_):
                                                    return (d_1005_d_, (MiscTypes.default__.SeqToSet((pat_let_tv13_).PredNat(pat_let_tv14_)) if (d_1005_d_) > ((pat_let_tv15_)[pat_let_tv16_]) else _dafny.Set({})))
                                                return iife37_(_pat_let17_0)
                                            return iife36_((d_1000_seg_).FastWeakestPreOperands(d_1004_m_, (pat_let_tv11_)[pat_let_tv12_]))
                                        return iife35_(_pat_let16_0)
                                    return iife34_(EVMObj.MaxNatSeq(d_1003_succWPre_))
                                return iife33_(_pat_let15_0)
                            return iife32_(MiscTypes.default__.MapP((pat_let_tv8_).SuccNat(pat_let_tv9_), lambda50_(pat_let_tv10_)))
                        return iife31_(_pat_let14_0)
                    d_999_n_ = (iife30_(((_this).xs)[(((a).states)[index]).segNum]) if (index) in (xu) else ((xc)[index], _dafny.Set({})))
                    in153_ = _this
                    in154_ = a
                    in155_ = wpre0
                    in156_ = xc
                    in157_ = xu
                    in158_ = (newxc) + (_dafny.SeqWithoutIsStrInference([(d_999_n_)[0]]))
                    in159_ = (newxu) | ((d_999_n_)[1])
                    in160_ = (index) + (1)
                    _this = in153_
                    
                    a = in154_
                    wpre0 = in155_
                    xc = in156_
                    xu = in157_
                    newxc = in158_
                    newxu = in159_
                    index = in160_
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
        def lambda52_(d_1008_a_):
            def lambda53_(d_1009_i_):
                return (((self).xs)[(((d_1008_a_).states)[d_1009_i_]).segNum]).WeakestPreOperands((((self).xs)[(((d_1008_a_).states)[d_1009_i_]).segNum]).Ins(), 0)

            return lambda53_

        d_1006_wpre0_ = MiscTypes.default__.MapP(_dafny.SeqWithoutIsStrInference([d_1007_i_ for d_1007_i_ in range(len((a).states))]), lambda52_(a))
        def iife38_():
            coll3_ = _dafny.Set()
            compr_3_: int
            for compr_3_ in _dafny.IntegerRange(0, len((a).states)):
                d_1010_z_: int = compr_3_
                if ((0) <= (d_1010_z_)) and ((d_1010_z_) < (len((a).states))):
                    coll3_ = coll3_.union(_dafny.Set([d_1010_z_]))
            return _dafny.Set(coll3_)
        return (self).Fix(a, d_1006_wpre0_, iife38_()
        , d_1006_wpre0_, (len((a).states)) + (1))

    def HasNoErrorState(self, a):
        def lambda54_(forall_var_10_):
            d_1011_s_: CFGState.GState = forall_var_10_
            return not ((d_1011_s_) in ((a).states)) or ((d_1011_s_).is_EGState)

        return _dafny.quantifier(((a).states).UniqueElements, True, lambda54_)

    def PrintByteCodeInfo(self):
        d_1012_listIns_: _dafny.Seq
        def lambda55_(d_1013_s_):
            return (d_1013_s_).Ins()

        d_1012_listIns_ = MiscTypes.default__.Flatten(MiscTypes.default__.Map((self).xs, lambda55_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bytecode Size: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of((self).Size((self).xs)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " Bytes\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Number of instructions: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len(d_1012_listIns_)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Arithmetic opcodes: "))).VerbatimString(False))
        def lambda56_(d_1014_i_):
            return ((d_1014_i_).op).is_ArithOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda56_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Comparison opcodes: "))).VerbatimString(False))
        def lambda57_(d_1015_i_):
            return ((d_1015_i_).op).is_CompOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda57_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise opcodes: "))).VerbatimString(False))
        def lambda58_(d_1016_i_):
            return ((d_1016_i_).op).is_BitwiseOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda58_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Keccak opcodes: "))).VerbatimString(False))
        def lambda59_(d_1017_i_):
            return ((d_1017_i_).op).is_KeccakOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda59_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Environmental opcodes: "))).VerbatimString(False))
        def lambda60_(d_1018_i_):
            return ((d_1018_i_).op).is_EnvOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda60_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage opcodes: "))).VerbatimString(False))
        def lambda61_(d_1019_i_):
            return ((d_1019_i_).op).is_StorageOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda61_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Memory opcodes: "))).VerbatimString(False))
        def lambda62_(d_1020_i_):
            return ((d_1020_i_).op).is_MemOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda62_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack opcodes: "))).VerbatimString(False))
        def lambda63_(d_1021_i_):
            return ((d_1021_i_).op).is_StackOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda63_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump opcodes: "))).VerbatimString(False))
        def lambda64_(d_1022_i_):
            return ((d_1022_i_).op).is_JumpOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda64_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Log opcodes: "))).VerbatimString(False))
        def lambda65_(d_1023_i_):
            return ((d_1023_i_).op).is_LogOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda65_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Revert/stop opcodes: "))).VerbatimString(False))
        def lambda66_(d_1024_i_):
            return (((d_1024_i_).op).is_SysOp) and (((d_1024_i_).op).IsRevertStop())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda66_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Return opcodes: "))).VerbatimString(False))
        def lambda67_(d_1025_i_):
            return (((d_1025_i_).op).is_SysOp) and (((d_1025_i_).op).IsReturn())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda67_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Invalid opcodes: "))).VerbatimString(False))
        def lambda68_(d_1026_i_):
            return (((d_1026_i_).op).is_SysOp) and (((d_1026_i_).op).IsInvalid())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda68_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Other Systems opcodes: "))).VerbatimString(False))
        def lambda69_(d_1027_i_):
            return (((((d_1027_i_).op).is_SysOp) and (not(((d_1027_i_).op).IsInvalid()))) and (not(((d_1027_i_).op).IsRevertStop()))) and (not(((d_1027_i_).op).IsReturn()))

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_1012_listIns_, lambda69_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def PrintSegmentInfo(self):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Total number of segments: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len((self).xs)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of JUMP segments: "))).VerbatimString(False))
        def lambda70_(d_1028_s_):
            return (d_1028_s_).is_JUMPSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda70_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of JUMPI segments: "))).VerbatimString(False))
        def lambda71_(d_1029_s_):
            return (d_1029_s_).is_JUMPISeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda71_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of RETURN segments: "))).VerbatimString(False))
        def lambda72_(d_1030_s_):
            return (d_1030_s_).is_RETURNSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda72_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of STOP segments: "))).VerbatimString(False))
        def lambda73_(d_1031_s_):
            return (d_1031_s_).is_STOPSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda73_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of CONT segments: "))).VerbatimString(False))
        def lambda74_(d_1032_s_):
            return (d_1032_s_).is_CONTSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda74_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of INVALID segments: "))).VerbatimString(False))
        def lambda75_(d_1033_s_):
            return (d_1033_s_).is_INVALIDSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda75_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))


class EVMObj_EVMObj(EVMObj, NamedTuple('EVMObj', [('xs', Any), ('jumpDests', Any), ('PCToSegMap', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMObject.EVMObj.EVMObj({_dafny.string_of(self.xs)}, {_dafny.string_of(self.jumpDests)}, {_dafny.string_of(self.PCToSegMap)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, EVMObj_EVMObj) and self.xs == __o.xs and self.jumpDests == __o.jumpDests and self.PCToSegMap == __o.PCToSegMap
    def __hash__(self) -> int:
        return super().__hash__()

