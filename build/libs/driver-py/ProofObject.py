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

# Module: ProofObject


class StackResolver:
    @classmethod
    def default(cls, ):
        return lambda: _dafny.Map({})
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_StackResolver(self) -> bool:
        return isinstance(self, StackResolver_StackResolver)

class StackResolver_StackResolver(StackResolver, NamedTuple('StackResolver', [('sp', Any)])):
    def __dafnystr__(self) -> str:
        return f'ProofObject.StackResolver.StackResolver({_dafny.string_of(self.sp)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, StackResolver_StackResolver) and self.sp == __o.sp
    def __hash__(self) -> int:
        return super().__hash__()


class ProofObj:
    @classmethod
    def default(cls, ):
        return lambda: ProofObj_JUMP(LinSegments.ValidLinSeg.default(), int(0), int(0), MiscTypes.Either.default(StackElement.StackElem.default())(), _dafny.Map({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_JUMP(self) -> bool:
        return isinstance(self, ProofObj_JUMP)
    @property
    def is_CONT(self) -> bool:
        return isinstance(self, ProofObj_CONT)
    @property
    def is_TERMINAL(self) -> bool:
        return isinstance(self, ProofObj_TERMINAL)
    def IsValid(self):
        source0_ = self
        if True:
            if source0_.is_JUMP:
                return (((self).s).is_JUMPSeg) or (((self).s).is_JUMPISeg)
        if True:
            if source0_.is_CONT:
                return ((self).s).is_CONTSeg
        if True:
            return ((((self).s).is_RETURNSeg) or (((self).s).is_STOPSeg)) or (((self).s).is_INVALIDSeg)

    def CollectJumpDest(self):
        return ((self).s).CollectJumpDest()

    def StackEffect(self):
        return ((self).s).StackEffect()


class ProofObj_JUMP(ProofObj, NamedTuple('JUMP', [('s', Any), ('wpOp', Any), ('wpCap', Any), ('tgt', Any), ('stacks', Any)])):
    def __dafnystr__(self) -> str:
        return f'ProofObject.ProofObj.JUMP({_dafny.string_of(self.s)}, {_dafny.string_of(self.wpOp)}, {_dafny.string_of(self.wpCap)}, {_dafny.string_of(self.tgt)}, {_dafny.string_of(self.stacks)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, ProofObj_JUMP) and self.s == __o.s and self.wpOp == __o.wpOp and self.wpCap == __o.wpCap and self.tgt == __o.tgt and self.stacks == __o.stacks
    def __hash__(self) -> int:
        return super().__hash__()

class ProofObj_CONT(ProofObj, NamedTuple('CONT', [('s', Any), ('wpOp', Any), ('wpCap', Any), ('stacks', Any)])):
    def __dafnystr__(self) -> str:
        return f'ProofObject.ProofObj.CONT({_dafny.string_of(self.s)}, {_dafny.string_of(self.wpOp)}, {_dafny.string_of(self.wpCap)}, {_dafny.string_of(self.stacks)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, ProofObj_CONT) and self.s == __o.s and self.wpOp == __o.wpOp and self.wpCap == __o.wpCap and self.stacks == __o.stacks
    def __hash__(self) -> int:
        return super().__hash__()

class ProofObj_TERMINAL(ProofObj, NamedTuple('TERMINAL', [('s', Any), ('wpOp', Any), ('wpCap', Any), ('stacks', Any)])):
    def __dafnystr__(self) -> str:
        return f'ProofObject.ProofObj.TERMINAL({_dafny.string_of(self.s)}, {_dafny.string_of(self.wpOp)}, {_dafny.string_of(self.wpCap)}, {_dafny.string_of(self.stacks)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, ProofObj_TERMINAL) and self.s == __o.s and self.wpOp == __o.wpOp and self.wpCap == __o.wpCap and self.stacks == __o.stacks
    def __hash__(self) -> int:
        return super().__hash__()

