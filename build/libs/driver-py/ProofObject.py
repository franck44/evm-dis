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
        source49_ = self
        if source49_.is_JUMP:
            d_745___mcc_h0_ = source49_.s
            d_746___mcc_h1_ = source49_.wpOp
            d_747___mcc_h2_ = source49_.wpCap
            d_748___mcc_h3_ = source49_.tgt
            d_749___mcc_h4_ = source49_.stacks
            return (((self).s).is_JUMPSeg) or (((self).s).is_JUMPISeg)
        elif source49_.is_CONT:
            d_750___mcc_h5_ = source49_.s
            d_751___mcc_h6_ = source49_.wpOp
            d_752___mcc_h7_ = source49_.wpCap
            d_753___mcc_h8_ = source49_.stacks
            return ((self).s).is_CONTSeg
        elif True:
            d_754___mcc_h9_ = source49_.s
            d_755___mcc_h10_ = source49_.wpOp
            d_756___mcc_h11_ = source49_.wpCap
            d_757___mcc_h12_ = source49_.stacks
            return ((((self).s).is_RETURNSeg) or (((self).s).is_STOPSeg)) or (((self).s).is_INVALIDSeg)

    def CollectJumpDest(self):
        return ((self).s).CollectJumpDest(((self).s).Ins())

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

