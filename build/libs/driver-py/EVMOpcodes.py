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

# Module: EVMOpcodes


class ValidOpcode:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "STOP")), EVMConstants.default__.STOP, 0, 0, 0, 0)
    def _Is(source__):
        d_0_x_: Opcode = source__
        return (d_0_x_).IsValid()

class Opcode:
    @classmethod
    def default(cls, ):
        return lambda: Opcode_ArithOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), int(0), int(0), int(0), int(0), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ArithOp(self) -> bool:
        return isinstance(self, Opcode_ArithOp)
    @property
    def is_CompOp(self) -> bool:
        return isinstance(self, Opcode_CompOp)
    @property
    def is_BitwiseOp(self) -> bool:
        return isinstance(self, Opcode_BitwiseOp)
    @property
    def is_KeccakOp(self) -> bool:
        return isinstance(self, Opcode_KeccakOp)
    @property
    def is_EnvOp(self) -> bool:
        return isinstance(self, Opcode_EnvOp)
    @property
    def is_MemOp(self) -> bool:
        return isinstance(self, Opcode_MemOp)
    @property
    def is_StorageOp(self) -> bool:
        return isinstance(self, Opcode_StorageOp)
    @property
    def is_JumpOp(self) -> bool:
        return isinstance(self, Opcode_JumpOp)
    @property
    def is_RunOp(self) -> bool:
        return isinstance(self, Opcode_RunOp)
    @property
    def is_StackOp(self) -> bool:
        return isinstance(self, Opcode_StackOp)
    @property
    def is_LogOp(self) -> bool:
        return isinstance(self, Opcode_LogOp)
    @property
    def is_SysOp(self) -> bool:
        return isinstance(self, Opcode_SysOp)
    def IsValid(self):
        source0_ = self
        if True:
            if source0_.is_ArithOp:
                return ((((EVMConstants.default__.ADD) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SIGNEXTEND))) and (((self).pops) == (2))) and (((self).pushes) == (1))
        if True:
            if source0_.is_CompOp:
                return (((EVMConstants.default__.LT) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.ISZERO))) and (((self).pops) >= ((self).pushes))
        if True:
            if source0_.is_BitwiseOp:
                return (((EVMConstants.default__.AND) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SAR))) and (((self).pops) >= ((self).pushes))
        if True:
            if source0_.is_KeccakOp:
                return ((((self).opcode) == (EVMConstants.default__.KECCAK256)) and (((self).pops) == (2))) and (((self).pushes) == (1))
        if True:
            if source0_.is_EnvOp:
                return (((EVMConstants.default__.ADDRESS) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.BASEFEE))) and (((((((self).pushes) == (1)) and (((self).pops) == (0))) or ((((self).pushes) == (1)) and (((self).pops) == (1)))) or ((((self).pushes) == (0)) and (((self).pops) == (3)))) or ((((self).pushes) == (0)) and (((self).pops) == (4))))
        if True:
            if source0_.is_MemOp:
                return ((((self).opcode) == (EVMConstants.default__.MLOAD)) and ((((self).pushes) == ((self).pops)) and (((self).pops) == (1)))) or (((((EVMConstants.default__.MSTORE) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.MSTORE8))) and (((self).pushes) == (0))) and (((self).pops) == (2)))
        if True:
            if source0_.is_StorageOp:
                return (((EVMConstants.default__.SLOAD) == ((self).opcode)) and ((((self).pushes) == ((self).pops)) and (((self).pops) == (1)))) or (((((self).opcode) == (EVMConstants.default__.SSTORE)) and (((self).pushes) == (0))) and (((self).pops) == (2)))
        if True:
            if source0_.is_JumpOp:
                return ((((EVMConstants.default__.JUMP) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.JUMPI))) or (((EVMConstants.default__.JUMPDEST) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.RJUMPV)))) and (((self).pushes) == (0))
        if True:
            if source0_.is_RunOp:
                return ((((EVMConstants.default__.PC) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.GAS))) and (((self).pops) == (0))) and (((self).pushes) == (1))
        if True:
            if source0_.is_StackOp:
                return ((((((self).opcode) == (EVMConstants.default__.POP)) and (((self).pushes) == (0))) and (((self).pops) == (1))) or (((((EVMConstants.default__.PUSH0) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.DUP16))) and (((self).pushes) == (1))) and (((self).pops) == (0)))) or ((((EVMConstants.default__.SWAP1) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SWAP16))) and ((((self).pushes) == ((self).pops)) and (((self).pops) == (0))))
        if True:
            if source0_.is_LogOp:
                return ((((EVMConstants.default__.LOG0) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.LOG4))) and (((self).pushes) == (0))) and (((self).pops) == ((((self).opcode) - (EVMConstants.default__.LOG0)) + (2)))
        if True:
            return (((((self).opcode) == (EVMConstants.default__.STOP)) or (((self).opcode) == (EVMConstants.default__.EOF))) or (((EVMConstants.default__.CREATE) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SELFDESTRUCT)))) and (((self).pushes) <= (1))

    def Args(self):
        if ((EVMConstants.default__.PUSH1) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.PUSH32)):
            return ((self).opcode) - (EVMConstants.default__.PUSH0)
        elif True:
            return 0

    def IsTerminal(self):
        source0_ = (self).opcode
        if True:
            if (source0_) == (0):
                return True
        if True:
            if (source0_) == (86):
                return True
        if True:
            if (source0_) == (87):
                return True
        if True:
            if (source0_) == (92):
                return True
        if True:
            if (source0_) == (93):
                return True
        if True:
            if (source0_) == (94):
                return True
        if True:
            if (source0_) == (243):
                return True
        if True:
            if (source0_) == (253):
                return True
        if True:
            if (source0_) == (254):
                return True
        if True:
            return False

    def IsJump(self):
        source0_ = (self).opcode
        if True:
            if (source0_) == (86):
                return True
        if True:
            if (source0_) == (87):
                return True
        if True:
            return False

    def IsJumpDest(self):
        return ((self).opcode) == (EVMConstants.default__.JUMPDEST)

    def IsRevertStop(self):
        return (((self).opcode) == (EVMConstants.default__.REVERT)) or (((self).opcode) == (EVMConstants.default__.STOP))

    def IsReturn(self):
        return ((self).opcode) == (EVMConstants.default__.RETURN)

    def IsInvalid(self):
        return ((self).opcode) == (EVMConstants.default__.INVALID)

    def Name(self):
        return (self).name

    def StackEffect(self):
        return ((self).pushes) - ((self).pops)

    def WeakestPreOperands(self, post):
        return Int.default__.Max((self).minOperands, (post) - ((self).StackEffect()))

    def WeakestPreCapacity(self, post):
        return Int.default__.Max((self).minCapacity, (post) + ((self).StackEffect()))


class Opcode_ArithOp(Opcode, NamedTuple('ArithOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.ArithOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_ArithOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_CompOp(Opcode, NamedTuple('CompOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.CompOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_CompOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_BitwiseOp(Opcode, NamedTuple('BitwiseOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.BitwiseOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_BitwiseOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_KeccakOp(Opcode, NamedTuple('KeccakOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.KeccakOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_KeccakOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_EnvOp(Opcode, NamedTuple('EnvOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.EnvOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_EnvOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_MemOp(Opcode, NamedTuple('MemOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.MemOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_MemOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_StorageOp(Opcode, NamedTuple('StorageOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.StorageOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_StorageOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_JumpOp(Opcode, NamedTuple('JumpOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.JumpOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_JumpOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_RunOp(Opcode, NamedTuple('RunOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.RunOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_RunOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_StackOp(Opcode, NamedTuple('StackOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.StackOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_StackOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_LogOp(Opcode, NamedTuple('LogOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.LogOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_LogOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

class Opcode_SysOp(Opcode, NamedTuple('SysOp', [('name', Any), ('opcode', Any), ('minCapacity', Any), ('minOperands', Any), ('pushes', Any), ('pops', Any)])):
    def __dafnystr__(self) -> str:
        return f'EVMOpcodes.Opcode.SysOp({self.name.VerbatimString(True)}, {_dafny.string_of(self.opcode)}, {_dafny.string_of(self.minCapacity)}, {_dafny.string_of(self.minOperands)}, {_dafny.string_of(self.pushes)}, {_dafny.string_of(self.pops)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Opcode_SysOp) and self.name == __o.name and self.opcode == __o.opcode and self.minCapacity == __o.minCapacity and self.minOperands == __o.minOperands and self.pushes == __o.pushes and self.pops == __o.pops
    def __hash__(self) -> int:
        return super().__hash__()

