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
        d_80_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_80_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_80_x_) if (len(d_80_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def IsTerminal(self):
        return ((self).op).IsTerminal()

    def IsJumpDest(self):
        return ((self).op).IsJumpDest()

    def StackEffect(self):
        return ((self).op).StackEffect()

    def WeakestPreOperands(self, post):
        return ((self).op).WeakestPreOperands(post)

    def WeakestPreCapacity(self, post):
        return ((self).op).WeakestPreCapacity(post)

    def StackPosBackWardTracker(self, pos_k):
        source5_ = (self).op
        if source5_.is_ArithOp:
            d_81___mcc_h0_ = source5_.name
            d_82___mcc_h1_ = source5_.opcode
            d_83___mcc_h2_ = source5_.minCapacity
            d_84___mcc_h3_ = source5_.minOperands
            d_85___mcc_h4_ = source5_.pushes
            d_86___mcc_h5_ = source5_.pops
            d_87_pops_ = d_86___mcc_h5_
            d_88_pushes_ = d_85___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_87_pops_)) - (d_88_pushes_))
            elif True:
                return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0")))
        elif source5_.is_CompOp:
            d_89___mcc_h6_ = source5_.name
            d_90___mcc_h7_ = source5_.opcode
            d_91___mcc_h8_ = source5_.minCapacity
            d_92___mcc_h9_ = source5_.minOperands
            d_93___mcc_h10_ = source5_.pushes
            d_94___mcc_h11_ = source5_.pops
            d_95_pops_ = d_94___mcc_h11_
            d_96_pushes_ = d_93___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_95_pops_)) - (d_96_pushes_))
            elif True:
                return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0")))
        elif source5_.is_BitwiseOp:
            d_97___mcc_h12_ = source5_.name
            d_98___mcc_h13_ = source5_.opcode
            d_99___mcc_h14_ = source5_.minCapacity
            d_100___mcc_h15_ = source5_.minOperands
            d_101___mcc_h16_ = source5_.pushes
            d_102___mcc_h17_ = source5_.pops
            return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))
        elif source5_.is_KeccakOp:
            d_103___mcc_h18_ = source5_.name
            d_104___mcc_h19_ = source5_.opcode
            d_105___mcc_h20_ = source5_.minCapacity
            d_106___mcc_h21_ = source5_.minOperands
            d_107___mcc_h22_ = source5_.pushes
            d_108___mcc_h23_ = source5_.pops
            return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))
        elif source5_.is_EnvOp:
            d_109___mcc_h24_ = source5_.name
            d_110___mcc_h25_ = source5_.opcode
            d_111___mcc_h26_ = source5_.minCapacity
            d_112___mcc_h27_ = source5_.minOperands
            d_113___mcc_h28_ = source5_.pushes
            d_114___mcc_h29_ = source5_.pops
            return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))
        elif source5_.is_MemOp:
            d_115___mcc_h30_ = source5_.name
            d_116___mcc_h31_ = source5_.opcode
            d_117___mcc_h32_ = source5_.minCapacity
            d_118___mcc_h33_ = source5_.minOperands
            d_119___mcc_h34_ = source5_.pushes
            d_120___mcc_h35_ = source5_.pops
            return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))
        elif source5_.is_StorageOp:
            d_121___mcc_h36_ = source5_.name
            d_122___mcc_h37_ = source5_.opcode
            d_123___mcc_h38_ = source5_.minCapacity
            d_124___mcc_h39_ = source5_.minOperands
            d_125___mcc_h40_ = source5_.pushes
            d_126___mcc_h41_ = source5_.pops
            return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))
        elif source5_.is_JumpOp:
            d_127___mcc_h42_ = source5_.name
            d_128___mcc_h43_ = source5_.opcode
            d_129___mcc_h44_ = source5_.minCapacity
            d_130___mcc_h45_ = source5_.minOperands
            d_131___mcc_h46_ = source5_.pushes
            d_132___mcc_h47_ = source5_.pops
            d_133_opcode_ = d_128___mcc_h43_
            if (d_133_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_133_opcode_)) and ((d_133_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_134_k_ = ((d_133_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_134_k_))
            elif True:
                return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))
        elif source5_.is_RunOp:
            d_135___mcc_h48_ = source5_.name
            d_136___mcc_h49_ = source5_.opcode
            d_137___mcc_h50_ = source5_.minCapacity
            d_138___mcc_h51_ = source5_.minOperands
            d_139___mcc_h52_ = source5_.pushes
            d_140___mcc_h53_ = source5_.pops
            return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))
        elif source5_.is_StackOp:
            d_141___mcc_h54_ = source5_.name
            d_142___mcc_h55_ = source5_.opcode
            d_143___mcc_h56_ = source5_.minCapacity
            d_144___mcc_h57_ = source5_.minOperands
            d_145___mcc_h58_ = source5_.pushes
            d_146___mcc_h59_ = source5_.pops
            d_147_opcode_ = d_142___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_147_opcode_)) and ((d_147_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left((self).arg)
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_147_opcode_)) and ((d_147_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_147_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_147_opcode_)) and ((d_147_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_148_k_ = ((d_147_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_148_k_ if (pos_k) == (0) else (0 if (pos_k) == ((d_148_k_) + (1)) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source5_.is_LogOp:
            d_149___mcc_h60_ = source5_.name
            d_150___mcc_h61_ = source5_.opcode
            d_151___mcc_h62_ = source5_.minCapacity
            d_152___mcc_h63_ = source5_.minOperands
            d_153___mcc_h64_ = source5_.pushes
            d_154___mcc_h65_ = source5_.pops
            return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))
        elif True:
            d_155___mcc_h66_ = source5_.name
            d_156___mcc_h67_ = source5_.opcode
            d_157___mcc_h68_ = source5_.minCapacity
            d_158___mcc_h69_ = source5_.minOperands
            d_159___mcc_h70_ = source5_.pushes
            d_160___mcc_h71_ = source5_.pops
            return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented")))


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

