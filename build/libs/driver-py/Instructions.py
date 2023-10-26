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


class Instruction:
    @classmethod
    def default(cls, ):
        return lambda: Instruction_Instruction(EVMOpcodes.Opcode.default()(), _dafny.Seq({}), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Instruction(self) -> bool:
        return isinstance(self, Instruction_Instruction)
    def ToString(self):
        d_7_x_ = (self).arg
        return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_7_x_) if (len(d_7_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def IsTerminal(self):
        return ((self).op).IsTerminal()

    def StackEffect(self):
        return ((self).op).StackEffect()

    def WeakestPreOperands(self, post):
        return ((self).op).WeakestPreOperands(post)

    def WeakestPreCapacity(self, post):
        return ((self).op).WeakestPreCapacity(post)

    def StackPosBackWardTracker(self, pos_k):
        source4_ = (self).op
        if source4_.is_ArithOp:
            d_8___mcc_h0_ = source4_.name
            d_9___mcc_h1_ = source4_.opcode
            d_10___mcc_h2_ = source4_.minCapacity
            d_11___mcc_h3_ = source4_.minOperands
            d_12___mcc_h4_ = source4_.pushes
            d_13___mcc_h5_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif source4_.is_CompOp:
            d_14___mcc_h6_ = source4_.name
            d_15___mcc_h7_ = source4_.opcode
            d_16___mcc_h8_ = source4_.minCapacity
            d_17___mcc_h9_ = source4_.minOperands
            d_18___mcc_h10_ = source4_.pushes
            d_19___mcc_h11_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif source4_.is_BitwiseOp:
            d_20___mcc_h12_ = source4_.name
            d_21___mcc_h13_ = source4_.opcode
            d_22___mcc_h14_ = source4_.minCapacity
            d_23___mcc_h15_ = source4_.minOperands
            d_24___mcc_h16_ = source4_.pushes
            d_25___mcc_h17_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif source4_.is_KeccakOp:
            d_26___mcc_h18_ = source4_.name
            d_27___mcc_h19_ = source4_.opcode
            d_28___mcc_h20_ = source4_.minCapacity
            d_29___mcc_h21_ = source4_.minOperands
            d_30___mcc_h22_ = source4_.pushes
            d_31___mcc_h23_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif source4_.is_EnvOp:
            d_32___mcc_h24_ = source4_.name
            d_33___mcc_h25_ = source4_.opcode
            d_34___mcc_h26_ = source4_.minCapacity
            d_35___mcc_h27_ = source4_.minOperands
            d_36___mcc_h28_ = source4_.pushes
            d_37___mcc_h29_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif source4_.is_MemOp:
            d_38___mcc_h30_ = source4_.name
            d_39___mcc_h31_ = source4_.opcode
            d_40___mcc_h32_ = source4_.minCapacity
            d_41___mcc_h33_ = source4_.minOperands
            d_42___mcc_h34_ = source4_.pushes
            d_43___mcc_h35_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif source4_.is_StorageOp:
            d_44___mcc_h36_ = source4_.name
            d_45___mcc_h37_ = source4_.opcode
            d_46___mcc_h38_ = source4_.minCapacity
            d_47___mcc_h39_ = source4_.minOperands
            d_48___mcc_h40_ = source4_.pushes
            d_49___mcc_h41_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif source4_.is_JumpOp:
            d_50___mcc_h42_ = source4_.name
            d_51___mcc_h43_ = source4_.opcode
            d_52___mcc_h44_ = source4_.minCapacity
            d_53___mcc_h45_ = source4_.minOperands
            d_54___mcc_h46_ = source4_.pushes
            d_55___mcc_h47_ = source4_.pops
            d_56_opcode_ = d_51___mcc_h43_
            if (d_56_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif True:
                return MiscTypes.Either_Right(0)
        elif source4_.is_RunOp:
            d_57___mcc_h48_ = source4_.name
            d_58___mcc_h49_ = source4_.opcode
            d_59___mcc_h50_ = source4_.minCapacity
            d_60___mcc_h51_ = source4_.minOperands
            d_61___mcc_h52_ = source4_.pushes
            d_62___mcc_h53_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif source4_.is_StackOp:
            d_63___mcc_h54_ = source4_.name
            d_64___mcc_h55_ = source4_.opcode
            d_65___mcc_h56_ = source4_.minCapacity
            d_66___mcc_h57_ = source4_.minOperands
            d_67___mcc_h58_ = source4_.pushes
            d_68___mcc_h59_ = source4_.pops
            d_69_opcode_ = d_64___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_69_opcode_)) and ((d_69_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left((self).arg)
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_69_opcode_)) and ((d_69_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_69_opcode_) - (128) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_69_opcode_)) and ((d_69_opcode_) <= (EVMConstants.default__.SWAP16)):
                return MiscTypes.Either_Right(0)
            elif (d_69_opcode_) == (EVMConstants.default__.POP):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('b'), _dafny.CodePoint('a'), _dafny.CodePoint('d')]))
        elif source4_.is_LogOp:
            d_70___mcc_h60_ = source4_.name
            d_71___mcc_h61_ = source4_.opcode
            d_72___mcc_h62_ = source4_.minCapacity
            d_73___mcc_h63_ = source4_.minOperands
            d_74___mcc_h64_ = source4_.pushes
            d_75___mcc_h65_ = source4_.pops
            return MiscTypes.Either_Right(0)
        elif True:
            d_76___mcc_h66_ = source4_.name
            d_77___mcc_h67_ = source4_.opcode
            d_78___mcc_h68_ = source4_.minCapacity
            d_79___mcc_h69_ = source4_.minOperands
            d_80___mcc_h70_ = source4_.pushes
            d_81___mcc_h71_ = source4_.pops
            return MiscTypes.Either_Right(0)


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

