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

# Module: EVMOpcodes


class Opcode:
    @classmethod
    def default(cls, ):
        return lambda: Opcode_ArithOp(_dafny.Seq({}), int(0), int(0), int(0), int(0), int(0))
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
    def Args(self):
        if ((EVMConstants.default__.PUSH1) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.PUSH32)):
            return ((self).opcode) - (EVMConstants.default__.PUSH0)
        elif True:
            return 0

    def IsTerminal(self):
        if ((self).opcode) == (0):
            return True
        elif ((self).opcode) == (86):
            return True
        elif ((self).opcode) == (87):
            return True
        elif ((self).opcode) == (92):
            return True
        elif ((self).opcode) == (93):
            return True
        elif ((self).opcode) == (94):
            return True
        elif ((self).opcode) == (243):
            return True
        elif ((self).opcode) == (253):
            return True
        elif True:
            return False

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

