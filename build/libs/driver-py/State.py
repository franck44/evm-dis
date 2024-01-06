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
    def BuildInitState(c, initpc):
        d_165_s0_ = default__.DEFAULT__VALIDSTATE
        if (c).is_StCond:
            d_166_dt__update__tmp_h0_ = d_165_s0_
            d_167_dt__update_hpc_h0_ = initpc
            d_168_dt__update_hstack_h0_ = (c).BuildStack(_dafny.SeqWithoutIsStrInference([]), 0)
            return AState_EState(d_167_dt__update_hpc_h0_, d_168_dt__update_hstack_h0_)
        elif True:
            d_169_dt__update__tmp_h1_ = d_165_s0_
            d_170_dt__update_hpc_h1_ = initpc
            return AState_EState(d_170_dt__update_hpc_h1_, (d_169_dt__update__tmp_h1_).stack)

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
        source32_ = self
        if source32_.is_EState:
            d_171___mcc_h0_ = source32_.pc
            d_172___mcc_h1_ = source32_.stack
            d_173_stack_ = d_172___mcc_h1_
            d_174_pc_ = d_171___mcc_h0_
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(pc=0x"))) + (Hex.default__.NatToHex(d_174_pc_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " stack:[")))) + (StackElement.default__.StackToString(d_173_stack_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "])")))
        elif True:
            d_175___mcc_h2_ = source32_.msg
            d_176_m_ = d_175___mcc_h2_
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorState "))) + (d_176_m_)

    def Size(self):
        return len((self).stack)

    def PC(self):
        return (self).pc

    def Skip(self, n):
        d_177_dt__update__tmp_h0_ = self
        d_178_dt__update_hpc_h0_ = ((self).pc) + (n)
        return AState_EState(d_178_dt__update_hpc_h0_, (d_177_dt__update__tmp_h0_).stack)

    def Goto(self, tgt):
        d_179_dt__update__tmp_h0_ = self
        d_180_dt__update_hpc_h0_ = tgt
        return AState_EState(d_180_dt__update_hpc_h0_, (d_179_dt__update__tmp_h0_).stack)

    def Peek(self, k):
        return ((self).stack)[k]

    def Pop(self):
        return (self).PopN(1)

    def PopN(self, n):
        d_181_dt__update__tmp_h0_ = self
        d_182_dt__update_hstack_h0_ = _dafny.SeqWithoutIsStrInference(((self).stack)[n::])
        return AState_EState((d_181_dt__update__tmp_h0_).pc, d_182_dt__update_hstack_h0_)

    def Push(self, v):
        d_183_dt__update__tmp_h0_ = self
        d_184_dt__update_hstack_h0_ = (_dafny.SeqWithoutIsStrInference([v])) + ((self).stack)
        return AState_EState((d_183_dt__update__tmp_h0_).pc, d_184_dt__update_hstack_h0_)

    def PushNRandom(self, n):
        d_185_xr_ = _dafny.SeqWithoutIsStrInference([StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) for d_186___v0_ in range(n)])
        d_187_dt__update__tmp_h0_ = self
        d_188_dt__update_hstack_h0_ = (d_185_xr_) + ((self).stack)
        return AState_EState((d_187_dt__update__tmp_h0_).pc, d_188_dt__update_hstack_h0_)

    def Dup(self, n):
        d_189_nth_ = ((self).stack)[(n) - (1)]
        d_190_dt__update__tmp_h0_ = self
        d_191_dt__update_hstack_h0_ = (_dafny.SeqWithoutIsStrInference([d_189_nth_])) + ((self).stack)
        return AState_EState((d_190_dt__update__tmp_h0_).pc, d_191_dt__update_hstack_h0_)

    def Swap(self, n):
        d_192_nth_ = ((self).stack)[n]
        d_193_top_ = ((self).stack)[0]
        d_194_dt__update__tmp_h0_ = self
        d_195_dt__update_hstack_h0_ = (((self).stack).set(0, d_192_nth_)).set(n, d_193_top_)
        return AState_EState((d_194_dt__update__tmp_h0_).pc, d_195_dt__update_hstack_h0_)

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

