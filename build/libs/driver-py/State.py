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

    @staticmethod
    def StackToString(s):
        d_126___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_126___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_126___accumulator_ = (d_126___accumulator_) + ((((s)[0]).ToString()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ","))))
                    in11_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in11_
                    raise _dafny.TailCall()
                break

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
        source26_ = self
        if source26_.is_EState:
            d_127___mcc_h0_ = source26_.pc
            d_128___mcc_h1_ = source26_.stack
            d_129_stack_ = d_128___mcc_h1_
            d_130_pc_ = d_127___mcc_h0_
            return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "(pc=0x"))) + (Hex.default__.NatToHex(d_130_pc_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " stack:[")))) + (default__.StackToString(d_129_stack_))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "])")))
        elif True:
            d_131___mcc_h2_ = source26_.msg
            d_132_m_ = d_131___mcc_h2_
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ErrorState "))) + (d_132_m_)

    def Size(self):
        return len((self).stack)

    def PC(self):
        return (self).pc

    def Skip(self, n):
        d_133_dt__update__tmp_h0_ = self
        d_134_dt__update_hpc_h0_ = ((self).pc) + (n)
        return AState_EState(d_134_dt__update_hpc_h0_, (d_133_dt__update__tmp_h0_).stack)

    def Goto(self, tgt):
        d_135_dt__update__tmp_h0_ = self
        d_136_dt__update_hpc_h0_ = tgt
        return AState_EState(d_136_dt__update_hpc_h0_, (d_135_dt__update__tmp_h0_).stack)

    def Peek(self, k):
        return ((self).stack)[k]

    def Pop(self):
        return (self).PopN(1)

    def PopN(self, n):
        d_137_dt__update__tmp_h0_ = self
        d_138_dt__update_hstack_h0_ = _dafny.SeqWithoutIsStrInference(((self).stack)[n::])
        return AState_EState((d_137_dt__update__tmp_h0_).pc, d_138_dt__update_hstack_h0_)

    def Push(self, v):
        d_139_dt__update__tmp_h0_ = self
        d_140_dt__update_hstack_h0_ = (_dafny.SeqWithoutIsStrInference([v])) + ((self).stack)
        return AState_EState((d_139_dt__update__tmp_h0_).pc, d_140_dt__update_hstack_h0_)

    def PushNRandom(self, n):
        d_141_xr_ = _dafny.SeqWithoutIsStrInference([StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))) for d_142___v0_ in range(n)])
        d_143_dt__update__tmp_h0_ = self
        d_144_dt__update_hstack_h0_ = (d_141_xr_) + ((self).stack)
        return AState_EState((d_143_dt__update__tmp_h0_).pc, d_144_dt__update_hstack_h0_)

    def Dup(self, n):
        d_145_nth_ = ((self).stack)[(n) - (1)]
        d_146_dt__update__tmp_h0_ = self
        d_147_dt__update_hstack_h0_ = (_dafny.SeqWithoutIsStrInference([d_145_nth_])) + ((self).stack)
        return AState_EState((d_146_dt__update__tmp_h0_).pc, d_147_dt__update_hstack_h0_)

    def Swap(self, n):
        d_148_nth_ = ((self).stack)[n]
        d_149_top_ = ((self).stack)[0]
        d_150_dt__update__tmp_h0_ = self
        d_151_dt__update_hstack_h0_ = (((self).stack).set(0, d_148_nth_)).set(n, d_149_top_)
        return AState_EState((d_150_dt__update__tmp_h0_).pc, d_151_dt__update_hstack_h0_)


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

