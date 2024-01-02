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
        d_904___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_904___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_904___accumulator_ = (d_904___accumulator_) + (((xs)[0]).CollectJumpDest())
                    in112_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in112_
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
                    in113_ = xs
                    in114_ = (m).set(((xs)[index]).StartAddress(), index)
                    in115_ = (index) + (1)
                    xs = in113_
                    m = in114_
                    index = in115_
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
        d_905___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (len(ls)) == (0):
                    return (0) + (d_905___accumulator_)
                elif True:
                    d_905___accumulator_ = (d_905___accumulator_) + (((ls)[0]).Size(((ls)[0]).Ins()))
                    in116_ = _this
                    in117_ = _dafny.SeqWithoutIsStrInference((ls)[1::])
                    _this = in116_
                    
                    ls = in117_
                    raise _dafny.TailCall()
                break

    def NextG(self, s):
        source60_ = s
        if source60_.is_EGState:
            d_906___mcc_h0_ = source60_.segNum
            d_907___mcc_h1_ = source60_.st
            d_908_st_ = d_907___mcc_h1_
            d_909_segNum_ = d_906___mcc_h0_
            d_910_srcSeg_ = ((self).xs)[d_909_segNum_]
            d_911_src_ = State.AState_EState((d_910_srcSeg_).StartAddress(), d_908_st_)
            d_912_successors_ = _dafny.SeqWithoutIsStrInference([(d_910_srcSeg_).Run(d_911_src_, d_913_i_, (self).jumpDests) for d_913_i_ in range((d_910_srcSeg_).NumberOfExits())])
            def lambda45_(d_915_s_k_):
                def lambda46_(source61_):
                    if source61_.is_EState:
                        d_916___mcc_h3_ = source61_.pc
                        d_917___mcc_h4_ = source61_.stack
                        d_918_st_ = d_917___mcc_h4_
                        d_919_pc_ = d_916___mcc_h3_
                        if (d_919_pc_) in ((self).PCToSegMap):
                            return CFGState.GState_EGState(((self).PCToSegMap)[d_919_pc_], (d_915_s_k_).stack)
                        elif True:
                            return CFGState.GState_ErrorGState(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "NextG:  "))) + (Int.default__.NatToString(d_919_pc_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " not defined"))))
                    elif True:
                        d_920___mcc_h5_ = source61_.msg
                        d_921_msg_ = d_920___mcc_h5_
                        return CFGState.GState_ErrorGState(d_921_msg_)

                return lambda46_(d_915_s_k_)

            d_914_succGStates_ = MiscTypes.default__.Map(d_912_successors_, lambda45_)
            return d_914_succGStates_
        elif True:
            d_922___mcc_h2_ = source60_.msg
            return _dafny.SeqWithoutIsStrInference([])

    def RunAll(self, exits, s):
        _this = self
        while True:
            with _dafny.label():
                if (len(exits)) == (0):
                    return s
                elif ((s).pc) in ((_this).PCToSegMap):
                    d_923_seg_ = ((_this).PCToSegMap)[(s).pc]
                    if ((((_this).xs)[d_923_seg_]).NumberOfExits()) > ((exits)[0]):
                        d_924_s_k_ = (((_this).xs)[d_923_seg_]).Run(s, (exits)[0], (_this).jumpDests)
                        if (d_924_s_k_).is_EState:
                            in118_ = _this
                            in119_ = _dafny.SeqWithoutIsStrInference((exits)[1::])
                            in120_ = d_924_s_k_
                            _this = in118_
                            
                            exits = in119_
                            s = in120_
                            raise _dafny.TailCall()
                        elif True:
                            return State.AState_Error(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Successor state of "))) + ((s).ToString())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " is not an EState"))))
                    elif True:
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exit does not exist")))
                elif True:
                    return State.AState_Error((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No segment found for state "))) + ((s).ToString()))
                break

    def PreservesCond(self, c, exits, initpc):
        pat_let_tv6_ = initpc
        def iife28_(_pat_let13_0):
            def iife29_(d_926_dt__update__tmp_h0_):
                def iife30_(_pat_let14_0):
                    def iife31_(d_927_dt__update_hpc_h0_):
                        return State.AState_EState(d_927_dt__update_hpc_h0_, (d_926_dt__update__tmp_h0_).stack)
                    return iife31_(_pat_let14_0)
                return iife30_(pat_let_tv6_)
            return iife29_(_pat_let13_0)
        d_925_initState_ = iife28_(State.default__.BuildInitState(c, 0))
        d_928_endState_ = (self).RunAll(exits, d_925_initState_)
        if (d_928_endState_).is_EState:
            return (d_928_endState_).Sat(c)
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
                    d_929___mcc_h0_ = source62_.v
                    d_930_index_ = d_929___mcc_h0_
                    d_931_pathFromIndex_ = _dafny.SeqWithoutIsStrInference((pStates)[d_930_index_::])
                    d_932_exitsFromIndex_ = _dafny.SeqWithoutIsStrInference((pExits)[d_930_index_::])
                    d_933_segmentsOnPathFromIndex_ = _dafny.SeqWithoutIsStrInference([((d_931_pathFromIndex_)[d_934_i_]).segNum for d_934_i_ in range(len(d_931_pathFromIndex_))])
                    d_935_tgtCond_ = (((_this).xs)[(MiscTypes.default__.Last(pStates)).segNum]).LeadsTo((((_this).xs)[i]).StartAddress(), MiscTypes.default__.Last(pExits))
                    d_936_w1_ = LinSegments.default__.WPreSeqSegs(d_933_segmentsOnPathFromIndex_, d_932_exitsFromIndex_, d_935_tgtCond_, (_this).xs, (((_this).xs)[i]).StartAddress())
                    if (d_936_w1_).is_StTrue:
                        return MiscTypes.Option_Some(d_930_index_)
                    elif (d_936_w1_).is_StFalse:
                        return MiscTypes.Option_None()
                    elif (_this).PreservesCond(d_936_w1_, d_932_exitsFromIndex_, (((_this).xs)[i]).StartAddress()):
                        return MiscTypes.Option_Some(d_930_index_)
                    elif (0) < (len(d_931_pathFromIndex_)):
                        in121_ = _this
                        in122_ = i
                        in123_ = _dafny.SeqWithoutIsStrInference((d_931_pathFromIndex_)[1::])
                        in124_ = _dafny.SeqWithoutIsStrInference((d_932_exitsFromIndex_)[1::])
                        _this = in121_
                        
                        i = in122_
                        pStates = in123_
                        pExits = in124_
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
                        d_937___mcc_h0_ = source63_.segNum
                        d_938___mcc_h1_ = source63_.st
                        d_939_st_ = d_938___mcc_h1_
                        d_940_i_k_ = d_937___mcc_h0_
                        if (d_940_i_k_) == (i):
                            return MiscTypes.Option_Some(index)
                        elif True:
                            in125_ = _this
                            in126_ = i
                            in127_ = gs
                            in128_ = (index) + (1)
                            _this = in125_
                            
                            i = in126_
                            gs = in127_
                            index = in128_
                            raise _dafny.TailCall()
                    elif True:
                        d_941___mcc_h2_ = source63_.msg
                        d_942_m_ = d_941___mcc_h2_
                        return MiscTypes.Option_None()
                break

    def DFS(self, p, a, maxDepth, debugInfo, stats):
        a_k: Automata.Auto = Automata.ValidAuto.default()
        stats_k: Statistics.Stats = Statistics.Stats.default()()
        d_943_LastOnPath_: CFGState.GState
        d_943_LastOnPath_ = MiscTypes.default__.Last((p).states)
        if ((maxDepth) == (0)) or ((d_943_LastOnPath_).is_ErrorGState):
            d_944_stats_k_: Statistics.Stats
            d_944_stats_k_ = ((stats).SetMaxDepth() if (maxDepth) == (0) else stats)
            rhs0_ = a
            rhs1_ = d_944_stats_k_
            a_k = rhs0_
            stats_k = rhs1_
            return a_k, stats_k
        elif True:
            a_k = a
            stats_k = stats
            hi4_ = len((self).NextG(d_943_LastOnPath_))
            for d_945_i_ in range(0, hi4_):
                d_946_i__th__succ_: CFGState.GState
                d_946_i__th__succ_ = ((self).NextG(d_943_LastOnPath_))[d_945_i_]
                if (d_946_i__th__succ_).is_ErrorGState:
                    rhs2_ = (a_k).AddEdge(d_943_LastOnPath_, d_946_i__th__succ_)
                    rhs3_ = (stats_k).IncError()
                    a_k = rhs2_
                    stats_k = rhs3_
                elif (d_946_i__th__succ_) in ((a_k).indexOf):
                    rhs4_ = (a_k).AddEdge(d_943_LastOnPath_, ((a_k).states)[((a_k).indexOf)[d_946_i__th__succ_]])
                    rhs5_ = (stats_k).IncVisited()
                    a_k = rhs4_
                    stats_k = rhs5_
                elif not((((self).xs)[(d_943_LastOnPath_).segNum]).IsJump()):
                    out0_: Automata.Auto
                    out1_: Statistics.Stats
                    out0_, out1_ = (self).DFS(Path_Path(((p).states) + (_dafny.SeqWithoutIsStrInference([d_946_i__th__succ_])), ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_945_i_]))), (a_k).AddEdge(d_943_LastOnPath_, d_946_i__th__succ_), (maxDepth) - (1), debugInfo, stats_k)
                    a_k = out0_
                    stats_k = out1_
                elif True:
                    source64_ = (self).SafeLoopFound((d_946_i__th__succ_).segNum, (p).states, ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_945_i_])))
                    if source64_.is_None:
                        out2_: Automata.Auto
                        out3_: Statistics.Stats
                        out2_, out3_ = (self).DFS(Path_Path(((p).states) + (_dafny.SeqWithoutIsStrInference([d_946_i__th__succ_])), ((p).exits) + (_dafny.SeqWithoutIsStrInference([d_945_i_]))), (a_k).AddEdge(d_943_LastOnPath_, d_946_i__th__succ_), (maxDepth) - (1), debugInfo, stats_k)
                        a_k = out2_
                        stats_k = out3_
                    elif True:
                        d_947___mcc_h0_ = source64_.v
                        d_948_index_ = d_947___mcc_h0_
                        rhs6_ = (a_k).AddEdge(d_943_LastOnPath_, ((p).states)[d_948_index_])
                        rhs7_ = (stats_k).IncWpre()
                        a_k = rhs6_
                        stats_k = rhs7_
        return a_k, stats_k

    def BuildCFG(self, maxDepth, minimise):
        a: Automata.Auto = Automata.ValidAuto.default()
        stats: Statistics.Stats = Statistics.Stats.default()()
        d_949_a1_: Automata.Auto
        d_950_s1_: Statistics.Stats
        out4_: Automata.Auto
        out5_: Statistics.Stats
        out4_, out5_ = (self).DFS(Path_Path(_dafny.SeqWithoutIsStrInference([CFGState.default__.DEFAULT__GSTATE]), _dafny.SeqWithoutIsStrInference([])), (Automata.Auto_Auto(_dafny.Map({}), _dafny.SeqWithoutIsStrInference([]), _dafny.Map({}))).AddState(CFGState.default__.DEFAULT__GSTATE), maxDepth, True, Statistics.Stats_Stats(False, 0, 0, 0, (0, 0)))
        d_949_a1_ = out4_
        d_950_s1_ = out5_
        if (not(minimise)) or (((d_949_a1_).SSize()) == (0)):
            rhs8_ = d_949_a1_
            rhs9_ = d_950_s1_
            a = rhs8_
            stats = rhs9_
            return a, stats
        elif True:
            d_951_p1_: PartitionMod.Partition
            d_951_p1_ = PartitionMod.default__.MakeInit((d_949_a1_).SSize())
            d_952_e_: Callable
            def lambda47_(d_953_a1_):
                def lambda48_(d_954_x_, d_955_y_):
                    def lambda49_(source65_):
                        d_956___mcc_h0_ = source65_[0]
                        d_957___mcc_h1_ = source65_[1]
                        source66_ = d_956___mcc_h0_
                        if source66_.is_EGState:
                            d_958___mcc_h2_ = source66_.segNum
                            d_959___mcc_h3_ = source66_.st
                            source67_ = d_957___mcc_h1_
                            if source67_.is_EGState:
                                d_960___mcc_h6_ = source67_.segNum
                                d_961___mcc_h7_ = source67_.st
                                d_962_s2_ = d_960___mcc_h6_
                                d_963_s1_ = d_958___mcc_h2_
                                return (d_963_s1_) == (d_962_s2_)
                            elif True:
                                d_964___mcc_h10_ = source67_.msg
                                return False
                        elif True:
                            d_965___mcc_h12_ = source66_.msg
                            return False

                    return (True if (d_954_x_) == (d_955_y_) else lambda49_((((d_953_a1_).states)[d_954_x_], ((d_953_a1_).states)[d_955_y_])))

                return lambda48_

            d_952_e_ = lambda47_(d_949_a1_)
            d_966_p2_: PartitionMod.Partition
            d_966_p2_ = (d_951_p1_).ComputeFinest(d_952_e_)
            d_967_vp_: GStateMinimiser.Pair
            d_967_vp_ = GStateMinimiser.Pair_Pair(d_949_a1_, d_966_p2_)
            d_968_a2_: Automata.Auto
            d_968_a2_ = (d_967_vp_).Minimise()
            pat_let_tv7_ = d_949_a1_
            pat_let_tv8_ = d_949_a1_
            def iife32_(_pat_let15_0):
                def iife33_(d_969_dt__update__tmp_h0_):
                    def iife34_(_pat_let16_0):
                        def iife35_(d_970_dt__update_hnonMinimisedSize_h0_):
                            return Statistics.Stats_Stats((d_969_dt__update__tmp_h0_).maxDepthReached, (d_969_dt__update__tmp_h0_).visitedStates, (d_969_dt__update__tmp_h0_).wPreInvSuccess, (d_969_dt__update__tmp_h0_).errorState, d_970_dt__update_hnonMinimisedSize_h0_)
                        return iife35_(_pat_let16_0)
                    return iife34_(((pat_let_tv7_).SSize(), (pat_let_tv8_).TSize(0)))
                return iife33_(_pat_let15_0)
            rhs10_ = d_968_a2_
            rhs11_ = iife32_(d_950_s1_)
            a = rhs10_
            stats = rhs11_
            return a, stats
        return a, stats

    def ToHTML(self, a, withTable):
        if (a).is_ErrorGState:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"))
        elif withTable:
            return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<"))) + (HTML.default__.DOTSegTable(((self).xs)[(a).segNum], (a).segNum))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))
        elif True:
            return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<"))) + ((HTML.default__.DOTSeg(((self).xs)[(a).segNum], (a).segNum))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))

    def DotLabel(self, s, exit):
        d_971_lab_ = (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")) if (s).is_ErrorGState else ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Jump\",style=dashed")) if ((((self).xs)[(s).segNum]).IsJump()) and ((exit) == (((((self).xs)[(s).segNum]).NumberOfExits()) - (1))) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tooltip=\"Next\""))) if ((s).is_EGState) and ((exit) < ((((self).xs)[(s).segNum]).NumberOfExits())) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error Number of exits"))))
        return ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ["))) + (d_971_lab_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))

    def PrintByteCodeInfo(self):
        d_972_listIns_: _dafny.Seq
        def lambda50_(d_973_s_):
            return (d_973_s_).Ins()

        d_972_listIns_ = MiscTypes.default__.Flatten(MiscTypes.default__.Map((self).xs, lambda50_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bytecode Size: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of((self).Size((self).xs)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " Bytes\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Number of instructions: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len(d_972_listIns_)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Arithmetic opcodes: "))).VerbatimString(False))
        def lambda51_(d_974_i_):
            return ((d_974_i_).op).is_ArithOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda51_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Comparison opcodes: "))).VerbatimString(False))
        def lambda52_(d_975_i_):
            return ((d_975_i_).op).is_CompOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda52_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise opcodes: "))).VerbatimString(False))
        def lambda53_(d_976_i_):
            return ((d_976_i_).op).is_BitwiseOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda53_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Keccak opcodes: "))).VerbatimString(False))
        def lambda54_(d_977_i_):
            return ((d_977_i_).op).is_KeccakOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda54_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Environmental opcodes: "))).VerbatimString(False))
        def lambda55_(d_978_i_):
            return ((d_978_i_).op).is_EnvOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda55_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage opcodes: "))).VerbatimString(False))
        def lambda56_(d_979_i_):
            return ((d_979_i_).op).is_StorageOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda56_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Memory opcodes: "))).VerbatimString(False))
        def lambda57_(d_980_i_):
            return ((d_980_i_).op).is_MemOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda57_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack opcodes: "))).VerbatimString(False))
        def lambda58_(d_981_i_):
            return ((d_981_i_).op).is_StackOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda58_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump opcodes: "))).VerbatimString(False))
        def lambda59_(d_982_i_):
            return ((d_982_i_).op).is_JumpOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda59_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Log opcodes: "))).VerbatimString(False))
        def lambda60_(d_983_i_):
            return ((d_983_i_).op).is_LogOp

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda60_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Revert/stop opcodes: "))).VerbatimString(False))
        def lambda61_(d_984_i_):
            return (((d_984_i_).op).is_SysOp) and (((d_984_i_).op).IsRevertStop())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda61_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Return opcodes: "))).VerbatimString(False))
        def lambda62_(d_985_i_):
            return (((d_985_i_).op).is_SysOp) and (((d_985_i_).op).IsReturn())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda62_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Invalid opcodes: "))).VerbatimString(False))
        def lambda63_(d_986_i_):
            return (((d_986_i_).op).is_SysOp) and (((d_986_i_).op).IsInvalid())

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda63_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Other Systems opcodes: "))).VerbatimString(False))
        def lambda64_(d_987_i_):
            return (((((d_987_i_).op).is_SysOp) and (not(((d_987_i_).op).IsInvalid()))) and (not(((d_987_i_).op).IsRevertStop()))) and (not(((d_987_i_).op).IsReturn()))

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter(d_972_listIns_, lambda64_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    def PrintSegmentInfo(self):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Total number of segments: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len((self).xs)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of JUMP segments: "))).VerbatimString(False))
        def lambda65_(d_988_s_):
            return (d_988_s_).is_JUMPSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda65_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of JUMPI segments: "))).VerbatimString(False))
        def lambda66_(d_989_s_):
            return (d_989_s_).is_JUMPISeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda66_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of RETURN segments: "))).VerbatimString(False))
        def lambda67_(d_990_s_):
            return (d_990_s_).is_RETURNSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda67_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of STOP segments: "))).VerbatimString(False))
        def lambda68_(d_991_s_):
            return (d_991_s_).is_STOPSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda68_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of CONT segments: "))).VerbatimString(False))
        def lambda69_(d_992_s_):
            return (d_992_s_).is_CONTSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda69_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "# of INVALID segments: "))).VerbatimString(False))
        def lambda70_(d_993_s_):
            return (d_993_s_).is_INVALIDSeg

        _dafny.print(_dafny.string_of(len(MiscTypes.default__.Filter((self).xs, lambda70_))))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))


class EVMObj_EVMObj(EVMObj, NamedTuple('EVMObj', [('xs', Any), ('jumpDests', Any), ('PCToSegMap', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMObject.EVMObj.EVMObj({_dafny.string_of(self.xs)}, {_dafny.string_of(self.jumpDests)}, {_dafny.string_of(self.PCToSegMap)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, EVMObj_EVMObj) and self.xs == __o.xs and self.jumpDests == __o.jumpDests and self.PCToSegMap == __o.PCToSegMap
    def __hash__(self) -> int:
        return super().__hash__()

