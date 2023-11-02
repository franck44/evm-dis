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
    def IsValid(self):
        source0_ = self
        if source0_.is_ArithOp:
            d_0___mcc_h0_ = source0_.name
            d_1___mcc_h1_ = source0_.opcode
            d_2___mcc_h2_ = source0_.minCapacity
            d_3___mcc_h3_ = source0_.minOperands
            d_4___mcc_h4_ = source0_.pushes
            d_5___mcc_h5_ = source0_.pops
            return ((((EVMConstants.default__.ADD) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SIGNEXTEND))) and (((self).pops) == (2))) and (((self).pushes) == (1))
        elif source0_.is_CompOp:
            d_6___mcc_h6_ = source0_.name
            d_7___mcc_h7_ = source0_.opcode
            d_8___mcc_h8_ = source0_.minCapacity
            d_9___mcc_h9_ = source0_.minOperands
            d_10___mcc_h10_ = source0_.pushes
            d_11___mcc_h11_ = source0_.pops
            return (((EVMConstants.default__.LT) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.ISZERO))) and (((self).pops) >= ((self).pushes))
        elif source0_.is_BitwiseOp:
            d_12___mcc_h12_ = source0_.name
            d_13___mcc_h13_ = source0_.opcode
            d_14___mcc_h14_ = source0_.minCapacity
            d_15___mcc_h15_ = source0_.minOperands
            d_16___mcc_h16_ = source0_.pushes
            d_17___mcc_h17_ = source0_.pops
            return ((EVMConstants.default__.AND) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SAR))
        elif source0_.is_KeccakOp:
            d_18___mcc_h18_ = source0_.name
            d_19___mcc_h19_ = source0_.opcode
            d_20___mcc_h20_ = source0_.minCapacity
            d_21___mcc_h21_ = source0_.minOperands
            d_22___mcc_h22_ = source0_.pushes
            d_23___mcc_h23_ = source0_.pops
            return ((self).opcode) == (EVMConstants.default__.KECCAK256)
        elif source0_.is_EnvOp:
            d_24___mcc_h24_ = source0_.name
            d_25___mcc_h25_ = source0_.opcode
            d_26___mcc_h26_ = source0_.minCapacity
            d_27___mcc_h27_ = source0_.minOperands
            d_28___mcc_h28_ = source0_.pushes
            d_29___mcc_h29_ = source0_.pops
            return ((EVMConstants.default__.ADDRESS) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.BASEFEE))
        elif source0_.is_MemOp:
            d_30___mcc_h30_ = source0_.name
            d_31___mcc_h31_ = source0_.opcode
            d_32___mcc_h32_ = source0_.minCapacity
            d_33___mcc_h33_ = source0_.minOperands
            d_34___mcc_h34_ = source0_.pushes
            d_35___mcc_h35_ = source0_.pops
            return ((EVMConstants.default__.MLOAD) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.MSTORE8))
        elif source0_.is_StorageOp:
            d_36___mcc_h36_ = source0_.name
            d_37___mcc_h37_ = source0_.opcode
            d_38___mcc_h38_ = source0_.minCapacity
            d_39___mcc_h39_ = source0_.minOperands
            d_40___mcc_h40_ = source0_.pushes
            d_41___mcc_h41_ = source0_.pops
            return ((EVMConstants.default__.SLOAD) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SSTORE))
        elif source0_.is_JumpOp:
            d_42___mcc_h42_ = source0_.name
            d_43___mcc_h43_ = source0_.opcode
            d_44___mcc_h44_ = source0_.minCapacity
            d_45___mcc_h45_ = source0_.minOperands
            d_46___mcc_h46_ = source0_.pushes
            d_47___mcc_h47_ = source0_.pops
            return (((EVMConstants.default__.JUMP) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.JUMPI))) or (((EVMConstants.default__.JUMPDEST) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.RJUMPV)))
        elif source0_.is_RunOp:
            d_48___mcc_h48_ = source0_.name
            d_49___mcc_h49_ = source0_.opcode
            d_50___mcc_h50_ = source0_.minCapacity
            d_51___mcc_h51_ = source0_.minOperands
            d_52___mcc_h52_ = source0_.pushes
            d_53___mcc_h53_ = source0_.pops
            return ((EVMConstants.default__.PC) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.GAS))
        elif source0_.is_StackOp:
            d_54___mcc_h54_ = source0_.name
            d_55___mcc_h55_ = source0_.opcode
            d_56___mcc_h56_ = source0_.minCapacity
            d_57___mcc_h57_ = source0_.minOperands
            d_58___mcc_h58_ = source0_.pushes
            d_59___mcc_h59_ = source0_.pops
            return (((self).opcode) == (EVMConstants.default__.POP)) or (((EVMConstants.default__.PUSH0) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SWAP16)))
        elif source0_.is_LogOp:
            d_60___mcc_h60_ = source0_.name
            d_61___mcc_h61_ = source0_.opcode
            d_62___mcc_h62_ = source0_.minCapacity
            d_63___mcc_h63_ = source0_.minOperands
            d_64___mcc_h64_ = source0_.pushes
            d_65___mcc_h65_ = source0_.pops
            return ((EVMConstants.default__.LOG0) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.LOG4))
        elif True:
            d_66___mcc_h66_ = source0_.name
            d_67___mcc_h67_ = source0_.opcode
            d_68___mcc_h68_ = source0_.minCapacity
            d_69___mcc_h69_ = source0_.minOperands
            d_70___mcc_h70_ = source0_.pushes
            d_71___mcc_h71_ = source0_.pops
            return ((((self).opcode) == (EVMConstants.default__.STOP)) or (((self).opcode) == (EVMConstants.default__.EOF))) or (((EVMConstants.default__.CREATE) <= ((self).opcode)) and (((self).opcode) <= (EVMConstants.default__.SELFDESTRUCT)))

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

    def IsJump(self):
        if ((self).opcode) == (86):
            return True
        elif ((self).opcode) == (87):
            return True
        elif True:
            return False

    def IsJumpDest(self):
        return ((self).opcode) == (EVMConstants.default__.JUMPDEST)

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

