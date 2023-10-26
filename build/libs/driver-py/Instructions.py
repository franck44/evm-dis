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

# Module: Instructions


class ValidOpcode:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "STOP")), EVMConstants.default__.STOP, 0, 0, 0, 0)

class Instruction:
    @classmethod
    def default(cls, ):
        return lambda: Instruction_Instruction(ValidOpcode.default(), _dafny.Seq({}), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Instruction(self) -> bool:
        return isinstance(self, Instruction_Instruction)
    def ToString(self):
        d_92_x_ = (self).arg
        return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_92_x_) if (len(d_92_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def IsTerminal(self):
        return ((self).op).IsTerminal()

    def StackEffect(self):
        return ((self).op).StackEffect()

    def WeakestPreOperands(self, post):
        return ((self).op).WeakestPreOperands(post)

    def WeakestPreCapacity(self, post):
        return ((self).op).WeakestPreCapacity(post)

    def StackPosBackWardTracker(self, pos_k):
        source5_ = (self).op
        if source5_.is_ArithOp:
            d_93___mcc_h0_ = source5_.name
            d_94___mcc_h1_ = source5_.opcode
            d_95___mcc_h2_ = source5_.minCapacity
            d_96___mcc_h3_ = source5_.minOperands
            d_97___mcc_h4_ = source5_.pushes
            d_98___mcc_h5_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif source5_.is_CompOp:
            d_99___mcc_h6_ = source5_.name
            d_100___mcc_h7_ = source5_.opcode
            d_101___mcc_h8_ = source5_.minCapacity
            d_102___mcc_h9_ = source5_.minOperands
            d_103___mcc_h10_ = source5_.pushes
            d_104___mcc_h11_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif source5_.is_BitwiseOp:
            d_105___mcc_h12_ = source5_.name
            d_106___mcc_h13_ = source5_.opcode
            d_107___mcc_h14_ = source5_.minCapacity
            d_108___mcc_h15_ = source5_.minOperands
            d_109___mcc_h16_ = source5_.pushes
            d_110___mcc_h17_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif source5_.is_KeccakOp:
            d_111___mcc_h18_ = source5_.name
            d_112___mcc_h19_ = source5_.opcode
            d_113___mcc_h20_ = source5_.minCapacity
            d_114___mcc_h21_ = source5_.minOperands
            d_115___mcc_h22_ = source5_.pushes
            d_116___mcc_h23_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif source5_.is_EnvOp:
            d_117___mcc_h24_ = source5_.name
            d_118___mcc_h25_ = source5_.opcode
            d_119___mcc_h26_ = source5_.minCapacity
            d_120___mcc_h27_ = source5_.minOperands
            d_121___mcc_h28_ = source5_.pushes
            d_122___mcc_h29_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif source5_.is_MemOp:
            d_123___mcc_h30_ = source5_.name
            d_124___mcc_h31_ = source5_.opcode
            d_125___mcc_h32_ = source5_.minCapacity
            d_126___mcc_h33_ = source5_.minOperands
            d_127___mcc_h34_ = source5_.pushes
            d_128___mcc_h35_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif source5_.is_StorageOp:
            d_129___mcc_h36_ = source5_.name
            d_130___mcc_h37_ = source5_.opcode
            d_131___mcc_h38_ = source5_.minCapacity
            d_132___mcc_h39_ = source5_.minOperands
            d_133___mcc_h40_ = source5_.pushes
            d_134___mcc_h41_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif source5_.is_JumpOp:
            d_135___mcc_h42_ = source5_.name
            d_136___mcc_h43_ = source5_.opcode
            d_137___mcc_h44_ = source5_.minCapacity
            d_138___mcc_h45_ = source5_.minOperands
            d_139___mcc_h46_ = source5_.pushes
            d_140___mcc_h47_ = source5_.pops
            d_141_opcode_ = d_136___mcc_h43_
            if (d_141_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif True:
                return MiscTypes.Either_Right(0)
        elif source5_.is_RunOp:
            d_142___mcc_h48_ = source5_.name
            d_143___mcc_h49_ = source5_.opcode
            d_144___mcc_h50_ = source5_.minCapacity
            d_145___mcc_h51_ = source5_.minOperands
            d_146___mcc_h52_ = source5_.pushes
            d_147___mcc_h53_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif source5_.is_StackOp:
            d_148___mcc_h54_ = source5_.name
            d_149___mcc_h55_ = source5_.opcode
            d_150___mcc_h56_ = source5_.minCapacity
            d_151___mcc_h57_ = source5_.minOperands
            d_152___mcc_h58_ = source5_.pushes
            d_153___mcc_h59_ = source5_.pops
            d_154_opcode_ = d_149___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_154_opcode_)) and ((d_154_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left((self).arg)
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_154_opcode_)) and ((d_154_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_154_opcode_) - (128) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_154_opcode_)) and ((d_154_opcode_) <= (EVMConstants.default__.SWAP16)):
                return MiscTypes.Either_Right(0)
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source5_.is_LogOp:
            d_155___mcc_h60_ = source5_.name
            d_156___mcc_h61_ = source5_.opcode
            d_157___mcc_h62_ = source5_.minCapacity
            d_158___mcc_h63_ = source5_.minOperands
            d_159___mcc_h64_ = source5_.pushes
            d_160___mcc_h65_ = source5_.pops
            return MiscTypes.Either_Right(0)
        elif True:
            d_161___mcc_h66_ = source5_.name
            d_162___mcc_h67_ = source5_.opcode
            d_163___mcc_h68_ = source5_.minCapacity
            d_164___mcc_h69_ = source5_.minOperands
            d_165___mcc_h70_ = source5_.pushes
            d_166___mcc_h71_ = source5_.pops
            return MiscTypes.Either_Right(0)


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

