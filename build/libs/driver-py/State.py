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

# Module: State

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def checkPos(s, pos, val):
        if (len((s).stack)) <= (pos):
            return False
        elif True:
            return (((s).stack)[pos]) == (StackElement.StackElem_Value(val))

    @staticmethod
    def StackToString(s):
        d_151___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_151___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_151___accumulator_ = (d_151___accumulator_) + ((((s)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ","))))
                    in24_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in24_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def BuildInitState(c, initpc):
        d_152_s0_ = default__.DEFAULT__VALIDSTATE
        if (c).is_StCond:
            d_153_dt__update__tmp_h0_ = d_152_s0_
            d_154_dt__update_hpc_h0_ = initpc
            d_155_dt__update_hstack_h0_ = (c).BuildStack(_dafny.SeqWithoutIsStrInference([]), 0)
            return AState_EState(d_154_dt__update_hpc_h0_, d_155_dt__update_hstack_h0_)
        elif True:
            d_156_dt__update__tmp_h1_ = d_152_s0_
            d_157_dt__update_hpc_h1_ = initpc
            return AState_EState(d_157_dt__update_hpc_h1_, (d_156_dt__update__tmp_h1_).stack)

    @_dafny.classproperty
    def DEFAULT__VALIDSTATE(instance):
        return AState_EState(0, _dafny.SeqWithoutIsStrInference([]))

class ValidState:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.DEFAULT__VALIDSTATE

class AState:
    @classmethod
    def default(cls, ):
        return lambda: AState_EState(int(0), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_EState(self) -> bool:
        return isinstance(self, AState_EState)
    @property
    def is_Error(self) -> bool:
        return isinstance(self, AState_Error)
    def ToString(self):
        source31_ = self
        if source31_.is_EState:
            d_158___mcc_h0_ = source31_.pc
            d_159___mcc_h1_ = source31_.stack
            d_160_stack_ = d_159___mcc_h1_
            d_161_pc_ = d_158___mcc_h0_
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(pc=0x"))) + (Hex.default__.NatToHex(d_161_pc_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " stack:[")))) + (default__.StackToString(d_160_stack_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "])")))
        elif True:
            d_162___mcc_h2_ = source31_.msg
            d_163_m_ = d_162___mcc_h2_
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorState "))) + (d_163_m_)

    def Size(self):
        return len((self).stack)

    def PC(self):
        return (self).pc

    def Skip(self, n):
        d_164_dt__update__tmp_h0_ = self
        d_165_dt__update_hpc_h0_ = ((self).pc) + (n)
        return AState_EState(d_165_dt__update_hpc_h0_, (d_164_dt__update__tmp_h0_).stack)

    def Goto(self, tgt):
        d_166_dt__update__tmp_h0_ = self
        d_167_dt__update_hpc_h0_ = tgt
        return AState_EState(d_167_dt__update_hpc_h0_, (d_166_dt__update__tmp_h0_).stack)

    def Peek(self, k):
        return ((self).stack)[k]

    def Pop(self):
        return (self).PopN(1)

    def PopN(self, n):
        d_168_dt__update__tmp_h0_ = self
        d_169_dt__update_hstack_h0_ = _dafny.SeqWithoutIsStrInference(((self).stack)[n::])
        return AState_EState((d_168_dt__update__tmp_h0_).pc, d_169_dt__update_hstack_h0_)

    def Push(self, v):
        d_170_dt__update__tmp_h0_ = self
        d_171_dt__update_hstack_h0_ = (_dafny.SeqWithoutIsStrInference([v])) + ((self).stack)
        return AState_EState((d_170_dt__update__tmp_h0_).pc, d_171_dt__update_hstack_h0_)

    def PushNRandom(self, n):
        d_172_xr_ = _dafny.SeqWithoutIsStrInference([StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) for d_173___v0_ in range(n)])
        d_174_dt__update__tmp_h0_ = self
        d_175_dt__update_hstack_h0_ = (d_172_xr_) + ((self).stack)
        return AState_EState((d_174_dt__update__tmp_h0_).pc, d_175_dt__update_hstack_h0_)

    def Dup(self, n):
        d_176_nth_ = ((self).stack)[(n) - (1)]
        d_177_dt__update__tmp_h0_ = self
        d_178_dt__update_hstack_h0_ = (_dafny.SeqWithoutIsStrInference([d_176_nth_])) + ((self).stack)
        return AState_EState((d_177_dt__update__tmp_h0_).pc, d_178_dt__update_hstack_h0_)

    def Swap(self, n):
        d_179_nth_ = ((self).stack)[n]
        d_180_top_ = ((self).stack)[0]
        d_181_dt__update__tmp_h0_ = self
        d_182_dt__update_hstack_h0_ = (((self).stack).set(0, d_179_nth_)).set(n, d_180_top_)
        return AState_EState((d_181_dt__update__tmp_h0_).pc, d_182_dt__update_hstack_h0_)

    def Sat(self, c):
        if ((c).Size()) == (1):
            return default__.checkPos(self, ((c).trackedPos)[0], ((c).trackedVals)[0])
        elif True:
            return (default__.checkPos(self, ((c).trackedPos)[0], ((c).trackedVals)[0])) and ((self).Sat((c).Tail()))


class AState_EState(AState, NamedTuple('EState', [('pc', Any), ('stack', Any)])):
    def __dafnystr__(self) -> str:
        return f'State.AState.EState({_dafny.string_of(self.pc)}, {_dafny.string_of(self.stack)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, AState_EState) and self.pc == __o.pc and self.stack == __o.stack
    def __hash__(self) -> int:
        return super().__hash__()

class AState_Error(AState, NamedTuple('Error', [('msg', Any)])):
    def __dafnystr__(self) -> str:
        return f'State.AState.Error({self.msg.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, AState_Error) and self.msg == __o.msg
    def __hash__(self) -> int:
        return super().__hash__()

