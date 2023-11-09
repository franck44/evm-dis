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

# Module: State

class default__:
    def  __init__(self):
        pass

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
    def Size(self):
        return len((self).stack)

    def PC(self):
        return (self).pc

    def Skip(self, n):
        d_123_dt__update__tmp_h0_ = self
        d_124_dt__update_hpc_h0_ = ((self).pc) + (n)
        return AState_EState(d_124_dt__update_hpc_h0_, (d_123_dt__update__tmp_h0_).stack)

    def Goto(self, tgt):
        d_125_dt__update__tmp_h0_ = self
        d_126_dt__update_hpc_h0_ = tgt
        return AState_EState(d_126_dt__update_hpc_h0_, (d_125_dt__update__tmp_h0_).stack)

    def Peek(self, k):
        return ((self).stack)[k]

    def Pop(self):
        return (self).PopN(1)

    def PopN(self, n):
        d_127_dt__update__tmp_h0_ = self
        d_128_dt__update_hstack_h0_ = _dafny.SeqWithoutIsStrInference(((self).stack)[n::])
        return AState_EState((d_127_dt__update__tmp_h0_).pc, d_128_dt__update_hstack_h0_)

    def Push(self, v):
        d_129_dt__update__tmp_h0_ = self
        d_130_dt__update_hstack_h0_ = (_dafny.SeqWithoutIsStrInference([v])) + ((self).stack)
        return AState_EState((d_129_dt__update__tmp_h0_).pc, d_130_dt__update_hstack_h0_)

    def PushNRandom(self, n):
        d_131_xr_ = _dafny.SeqWithoutIsStrInference([StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) for d_132___v0_ in range(n)])
        d_133_dt__update__tmp_h0_ = self
        d_134_dt__update_hstack_h0_ = (d_131_xr_) + ((self).stack)
        return AState_EState((d_133_dt__update__tmp_h0_).pc, d_134_dt__update_hstack_h0_)

    def Dup(self, n):
        d_135_nth_ = ((self).stack)[(n) - (1)]
        d_136_dt__update__tmp_h0_ = self
        d_137_dt__update_hstack_h0_ = (_dafny.SeqWithoutIsStrInference([d_135_nth_])) + ((self).stack)
        return AState_EState((d_136_dt__update__tmp_h0_).pc, d_137_dt__update_hstack_h0_)

    def Swap(self, n):
        d_138_nth_ = ((self).stack)[n]
        d_139_top_ = ((self).stack)[0]
        d_140_dt__update__tmp_h0_ = self
        d_141_dt__update_hstack_h0_ = (((self).stack).set(0, d_138_nth_)).set(n, d_139_top_)
        return AState_EState((d_140_dt__update__tmp_h0_).pc, d_141_dt__update_hstack_h0_)


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

