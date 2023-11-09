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
import State
import WeakPre

# Module: Instructions

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetArgValuePush(xc):
        d_144_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_145___v134_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_144_pad_) + (xc))).Extract()


class ValidInstruction:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Instruction_Instruction(EVMOpcodes.Opcode_SysOp(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "STOP")), EVMConstants.default__.STOP, 0, 0, 0, 0), _dafny.SeqWithoutIsStrInference([]), 0)

class Instruction:
    @classmethod
    def default(cls, ):
        return lambda: Instruction_Instruction(EVMOpcodes.ValidOpcode.default(), _dafny.Seq({}), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Instruction(self) -> bool:
        return isinstance(self, Instruction_Instruction)
    def IsValid(self):
        def lambda2_(forall_var_2_):
            d_146_k_: int = forall_var_2_
            return not (((0) <= (d_146_k_)) and ((d_146_k_) < (len((self).arg)))) or (Hex.default__.IsHex(((self).arg)[d_146_k_]))

        return ((((self).op).opcode) == (EVMConstants.default__.INVALID)) or ((not (((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32))) or (((len((self).arg)) == ((2) * ((((self).op).opcode) - (EVMConstants.default__.PUSH0)))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).arg)), True, lambda2_)))) and (not (not(((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32)))) or ((len((self).arg)) == (0))))

    def ToString(self):
        d_147_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_147_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_147_x_) if (len(d_147_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

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
        source25_ = (self).op
        if source25_.is_ArithOp:
            d_148___mcc_h0_ = source25_.name
            d_149___mcc_h1_ = source25_.opcode
            d_150___mcc_h2_ = source25_.minCapacity
            d_151___mcc_h3_ = source25_.minOperands
            d_152___mcc_h4_ = source25_.pushes
            d_153___mcc_h5_ = source25_.pops
            d_154_pops_ = d_153___mcc_h5_
            d_155_pushes_ = d_152___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source25_.is_CompOp:
            d_156___mcc_h6_ = source25_.name
            d_157___mcc_h7_ = source25_.opcode
            d_158___mcc_h8_ = source25_.minCapacity
            d_159___mcc_h9_ = source25_.minOperands
            d_160___mcc_h10_ = source25_.pushes
            d_161___mcc_h11_ = source25_.pops
            d_162_pops_ = d_161___mcc_h11_
            d_163_pushes_ = d_160___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_162_pops_)) - (d_163_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source25_.is_BitwiseOp:
            d_164___mcc_h12_ = source25_.name
            d_165___mcc_h13_ = source25_.opcode
            d_166___mcc_h14_ = source25_.minCapacity
            d_167___mcc_h15_ = source25_.minOperands
            d_168___mcc_h16_ = source25_.pushes
            d_169___mcc_h17_ = source25_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source25_.is_KeccakOp:
            d_170___mcc_h18_ = source25_.name
            d_171___mcc_h19_ = source25_.opcode
            d_172___mcc_h20_ = source25_.minCapacity
            d_173___mcc_h21_ = source25_.minOperands
            d_174___mcc_h22_ = source25_.pushes
            d_175___mcc_h23_ = source25_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source25_.is_EnvOp:
            d_176___mcc_h24_ = source25_.name
            d_177___mcc_h25_ = source25_.opcode
            d_178___mcc_h26_ = source25_.minCapacity
            d_179___mcc_h27_ = source25_.minOperands
            d_180___mcc_h28_ = source25_.pushes
            d_181___mcc_h29_ = source25_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source25_.is_MemOp:
            d_182___mcc_h30_ = source25_.name
            d_183___mcc_h31_ = source25_.opcode
            d_184___mcc_h32_ = source25_.minCapacity
            d_185___mcc_h33_ = source25_.minOperands
            d_186___mcc_h34_ = source25_.pushes
            d_187___mcc_h35_ = source25_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source25_.is_StorageOp:
            d_188___mcc_h36_ = source25_.name
            d_189___mcc_h37_ = source25_.opcode
            d_190___mcc_h38_ = source25_.minCapacity
            d_191___mcc_h39_ = source25_.minOperands
            d_192___mcc_h40_ = source25_.pushes
            d_193___mcc_h41_ = source25_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source25_.is_JumpOp:
            d_194___mcc_h42_ = source25_.name
            d_195___mcc_h43_ = source25_.opcode
            d_196___mcc_h44_ = source25_.minCapacity
            d_197___mcc_h45_ = source25_.minOperands
            d_198___mcc_h46_ = source25_.pushes
            d_199___mcc_h47_ = source25_.pops
            d_200_opcode_ = d_195___mcc_h43_
            if (d_200_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_200_opcode_)) and ((d_200_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_201_k_ = ((d_200_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_201_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source25_.is_RunOp:
            d_202___mcc_h48_ = source25_.name
            d_203___mcc_h49_ = source25_.opcode
            d_204___mcc_h50_ = source25_.minCapacity
            d_205___mcc_h51_ = source25_.minOperands
            d_206___mcc_h52_ = source25_.pushes
            d_207___mcc_h53_ = source25_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source25_.is_StackOp:
            d_208___mcc_h54_ = source25_.name
            d_209___mcc_h55_ = source25_.opcode
            d_210___mcc_h56_ = source25_.minCapacity
            d_211___mcc_h57_ = source25_.minOperands
            d_212___mcc_h58_ = source25_.pushes
            d_213___mcc_h59_ = source25_.pops
            d_214_opcode_ = d_209___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_214_opcode_)) and ((d_214_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_214_opcode_)) and ((d_214_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_214_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_214_opcode_)) and ((d_214_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_215_k_ = ((d_214_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_215_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_215_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source25_.is_LogOp:
            d_216___mcc_h60_ = source25_.name
            d_217___mcc_h61_ = source25_.opcode
            d_218___mcc_h62_ = source25_.minCapacity
            d_219___mcc_h63_ = source25_.minOperands
            d_220___mcc_h64_ = source25_.pushes
            d_221___mcc_h65_ = source25_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif True:
            d_222___mcc_h66_ = source25_.name
            d_223___mcc_h67_ = source25_.opcode
            d_224___mcc_h68_ = source25_.minCapacity
            d_225___mcc_h69_ = source25_.minOperands
            d_226___mcc_h70_ = source25_.pushes
            d_227___mcc_h71_ = source25_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))

    def NextState(self, s, cond):
        source26_ = (self).op
        if source26_.is_ArithOp:
            d_228___mcc_h0_ = source26_.name
            d_229___mcc_h1_ = source26_.opcode
            d_230___mcc_h2_ = source26_.minCapacity
            d_231___mcc_h3_ = source26_.minOperands
            d_232___mcc_h4_ = source26_.pushes
            d_233___mcc_h5_ = source26_.pops
            d_234_pops_ = d_233___mcc_h5_
            d_235_pushes_ = d_232___mcc_h4_
            if (((s).Size()) >= (d_234_pops_)) and (not(cond)):
                return (((s).PopN(d_234_pops_)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source26_.is_CompOp:
            d_236___mcc_h6_ = source26_.name
            d_237___mcc_h7_ = source26_.opcode
            d_238___mcc_h8_ = source26_.minCapacity
            d_239___mcc_h9_ = source26_.minOperands
            d_240___mcc_h10_ = source26_.pushes
            d_241___mcc_h11_ = source26_.pops
            d_242_pops_ = d_241___mcc_h11_
            d_243_pushes_ = d_240___mcc_h10_
            if (((s).Size()) >= (d_242_pops_)) and (not(cond)):
                return (((s).PopN(d_242_pops_)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source26_.is_BitwiseOp:
            d_244___mcc_h12_ = source26_.name
            d_245___mcc_h13_ = source26_.opcode
            d_246___mcc_h14_ = source26_.minCapacity
            d_247___mcc_h15_ = source26_.minOperands
            d_248___mcc_h16_ = source26_.pushes
            d_249___mcc_h17_ = source26_.pops
            d_250_pops_ = d_249___mcc_h17_
            d_251_pushes_ = d_248___mcc_h16_
            if (((s).Size()) >= (d_250_pops_)) and (not(cond)):
                return (((s).PopN(d_250_pops_)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source26_.is_KeccakOp:
            d_252___mcc_h18_ = source26_.name
            d_253___mcc_h19_ = source26_.opcode
            d_254___mcc_h20_ = source26_.minCapacity
            d_255___mcc_h21_ = source26_.minOperands
            d_256___mcc_h22_ = source26_.pushes
            d_257___mcc_h23_ = source26_.pops
            d_258_pops_ = d_257___mcc_h23_
            d_259_pushes_ = d_256___mcc_h22_
            if (((s).Size()) >= (2)) and (not(cond)):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source26_.is_EnvOp:
            d_260___mcc_h24_ = source26_.name
            d_261___mcc_h25_ = source26_.opcode
            d_262___mcc_h26_ = source26_.minCapacity
            d_263___mcc_h27_ = source26_.minOperands
            d_264___mcc_h28_ = source26_.pushes
            d_265___mcc_h29_ = source26_.pops
            d_266_pops_ = d_265___mcc_h29_
            d_267_pushes_ = d_264___mcc_h28_
            if not(cond):
                return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))
        elif source26_.is_MemOp:
            d_268___mcc_h30_ = source26_.name
            d_269___mcc_h31_ = source26_.opcode
            d_270___mcc_h32_ = source26_.minCapacity
            d_271___mcc_h33_ = source26_.minOperands
            d_272___mcc_h34_ = source26_.pushes
            d_273___mcc_h35_ = source26_.pops
            d_274_pops_ = d_273___mcc_h35_
            d_275_pushes_ = d_272___mcc_h34_
            if (((s).Size()) >= (d_274_pops_)) and (not(cond)):
                return (((s).PopN(d_274_pops_)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))
        elif source26_.is_StorageOp:
            d_276___mcc_h36_ = source26_.name
            d_277___mcc_h37_ = source26_.opcode
            d_278___mcc_h38_ = source26_.minCapacity
            d_279___mcc_h39_ = source26_.minOperands
            d_280___mcc_h40_ = source26_.pushes
            d_281___mcc_h41_ = source26_.pops
            d_282_pops_ = d_281___mcc_h41_
            d_283_pushes_ = d_280___mcc_h40_
            if (((s).Size()) >= (d_282_pops_)) and (not(cond)):
                return (((s).PopN(d_282_pops_)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))
        elif source26_.is_JumpOp:
            d_284___mcc_h42_ = source26_.name
            d_285___mcc_h43_ = source26_.opcode
            d_286___mcc_h44_ = source26_.minCapacity
            d_287___mcc_h45_ = source26_.minOperands
            d_288___mcc_h46_ = source26_.pushes
            d_289___mcc_h47_ = source26_.pops
            d_290_pops_ = d_289___mcc_h47_
            d_291_pushes_ = d_288___mcc_h46_
            d_292_opcode_ = d_285___mcc_h43_
            if (d_292_opcode_) == (EVMConstants.default__.JUMPDEST):
                if not(cond):
                    return (s).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPDEST/exit true")))
            elif (d_292_opcode_) == (EVMConstants.default__.JUMP):
                if (((s).Size()) >= (1)) and (cond):
                    source27_ = (s).Peek(0)
                    if source27_.is_Value:
                        d_293___mcc_h72_ = source27_.v
                        d_294_v_ = d_293___mcc_h72_
                        return ((s).Pop()).Goto(d_294_v_)
                    elif True:
                        d_295___mcc_h73_ = source27_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_292_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source28_ = (s).Peek(0)
                    if source28_.is_Value:
                        d_296___mcc_h74_ = source28_.v
                        d_297_v_ = d_296___mcc_h74_
                        if cond:
                            return ((s).PopN(2)).Goto(d_297_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_298___mcc_h75_ = source28_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source26_.is_RunOp:
            d_299___mcc_h48_ = source26_.name
            d_300___mcc_h49_ = source26_.opcode
            d_301___mcc_h50_ = source26_.minCapacity
            d_302___mcc_h51_ = source26_.minOperands
            d_303___mcc_h52_ = source26_.pushes
            d_304___mcc_h53_ = source26_.pops
            d_305_pops_ = d_304___mcc_h53_
            d_306_pushes_ = d_303___mcc_h52_
            if not(cond):
                return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))
        elif source26_.is_StackOp:
            d_307___mcc_h54_ = source26_.name
            d_308___mcc_h55_ = source26_.opcode
            d_309___mcc_h56_ = source26_.minCapacity
            d_310___mcc_h57_ = source26_.minOperands
            d_311___mcc_h58_ = source26_.pushes
            d_312___mcc_h59_ = source26_.pops
            d_313_pops_ = d_312___mcc_h59_
            d_314_pushes_ = d_311___mcc_h58_
            d_315_opcode_ = d_308___mcc_h55_
            if (((d_315_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1))) and (not(cond)):
                return ((s).Pop()).Skip(1)
            elif (((EVMConstants.default__.PUSH0) <= (d_315_opcode_)) and ((d_315_opcode_) <= (EVMConstants.default__.PUSH32))) and (not(cond)):
                return ((s).Push(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))).Skip((1) + ((d_315_opcode_) - (EVMConstants.default__.PUSH0)))
            elif ((((EVMConstants.default__.DUP1) <= (d_315_opcode_)) and ((d_315_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_315_opcode_) - (EVMConstants.default__.DUP1)) + (1)))) and (not(cond)):
                return ((s).Dup(((d_315_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif ((((EVMConstants.default__.SWAP1) <= (d_315_opcode_)) and ((d_315_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_315_opcode_) - (EVMConstants.default__.SWAP1)) + (1)))) and (not(cond)):
                return ((s).Swap(((d_315_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))
        elif source26_.is_LogOp:
            d_316___mcc_h60_ = source26_.name
            d_317___mcc_h61_ = source26_.opcode
            d_318___mcc_h62_ = source26_.minCapacity
            d_319___mcc_h63_ = source26_.minOperands
            d_320___mcc_h64_ = source26_.pushes
            d_321___mcc_h65_ = source26_.pops
            d_322_pops_ = d_321___mcc_h65_
            d_323_pushes_ = d_320___mcc_h64_
            if (((s).Size()) >= (d_322_pops_)) and (not(cond)):
                return ((s).PopN(d_322_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))
        elif True:
            d_324___mcc_h66_ = source26_.name
            d_325___mcc_h67_ = source26_.opcode
            d_326___mcc_h68_ = source26_.minCapacity
            d_327___mcc_h69_ = source26_.minOperands
            d_328___mcc_h70_ = source26_.pushes
            d_329___mcc_h71_ = source26_.pops
            d_330_pops_ = d_329___mcc_h71_
            d_331_pushes_ = d_328___mcc_h70_
            if (((s).Size()) >= (d_330_pops_)) and (not(cond)):
                return (((s).PopN(d_330_pops_)).PushNRandom(d_331_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Error")))

    def WPre(self, c):
        source29_ = (self).op
        if source29_.is_ArithOp:
            d_332___mcc_h0_ = source29_.name
            d_333___mcc_h1_ = source29_.opcode
            d_334___mcc_h2_ = source29_.minCapacity
            d_335___mcc_h3_ = source29_.minOperands
            d_336___mcc_h4_ = source29_.pushes
            d_337___mcc_h5_ = source29_.pops
            d_338_pops_ = d_337___mcc_h5_
            d_339_pushes_ = d_336___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda3_(d_341_pos_):
                    return (d_341_pos_) + (1)

                d_340_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda3_)
                return WeakPre.Cond_StCond(d_340_shiftByOne_, (c).TrackedVals())
        elif source29_.is_CompOp:
            d_342___mcc_h12_ = source29_.name
            d_343___mcc_h13_ = source29_.opcode
            d_344___mcc_h14_ = source29_.minCapacity
            d_345___mcc_h15_ = source29_.minOperands
            d_346___mcc_h16_ = source29_.pushes
            d_347___mcc_h17_ = source29_.pops
            d_348_pops_ = d_347___mcc_h17_
            d_349_pushes_ = d_346___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda4_(d_351_pops_, d_352_pushes_):
                    def lambda5_(d_353_pos_):
                        return ((d_353_pos_) + (d_351_pops_)) - (d_352_pushes_)

                    return lambda5_

                d_350_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda4_(d_348_pops_, d_349_pushes_))
                return WeakPre.Cond_StCond(d_350_shiftBy_, (c).TrackedVals())
        elif source29_.is_BitwiseOp:
            d_354___mcc_h24_ = source29_.name
            d_355___mcc_h25_ = source29_.opcode
            d_356___mcc_h26_ = source29_.minCapacity
            d_357___mcc_h27_ = source29_.minOperands
            d_358___mcc_h28_ = source29_.pushes
            d_359___mcc_h29_ = source29_.pops
            return c
        elif source29_.is_KeccakOp:
            d_360___mcc_h36_ = source29_.name
            d_361___mcc_h37_ = source29_.opcode
            d_362___mcc_h38_ = source29_.minCapacity
            d_363___mcc_h39_ = source29_.minOperands
            d_364___mcc_h40_ = source29_.pushes
            d_365___mcc_h41_ = source29_.pops
            return c
        elif source29_.is_EnvOp:
            d_366___mcc_h48_ = source29_.name
            d_367___mcc_h49_ = source29_.opcode
            d_368___mcc_h50_ = source29_.minCapacity
            d_369___mcc_h51_ = source29_.minOperands
            d_370___mcc_h52_ = source29_.pushes
            d_371___mcc_h53_ = source29_.pops
            return c
        elif source29_.is_MemOp:
            d_372___mcc_h60_ = source29_.name
            d_373___mcc_h61_ = source29_.opcode
            d_374___mcc_h62_ = source29_.minCapacity
            d_375___mcc_h63_ = source29_.minOperands
            d_376___mcc_h64_ = source29_.pushes
            d_377___mcc_h65_ = source29_.pops
            return c
        elif source29_.is_StorageOp:
            d_378___mcc_h72_ = source29_.name
            d_379___mcc_h73_ = source29_.opcode
            d_380___mcc_h74_ = source29_.minCapacity
            d_381___mcc_h75_ = source29_.minOperands
            d_382___mcc_h76_ = source29_.pushes
            d_383___mcc_h77_ = source29_.pops
            return c
        elif source29_.is_JumpOp:
            d_384___mcc_h84_ = source29_.name
            d_385___mcc_h85_ = source29_.opcode
            d_386___mcc_h86_ = source29_.minCapacity
            d_387___mcc_h87_ = source29_.minOperands
            d_388___mcc_h88_ = source29_.pushes
            d_389___mcc_h89_ = source29_.pops
            d_390_opcode_ = d_385___mcc_h85_
            if (d_390_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_390_opcode_)) and ((d_390_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_391_k_ = ((d_390_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda6_(d_393_k_):
                    def lambda7_(d_394_pos_):
                        return (d_394_pos_) + (d_393_k_)

                    return lambda7_

                d_392_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_(d_391_k_))
                return WeakPre.Cond_StCond(d_392_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source29_.is_RunOp:
            d_395___mcc_h96_ = source29_.name
            d_396___mcc_h97_ = source29_.opcode
            d_397___mcc_h98_ = source29_.minCapacity
            d_398___mcc_h99_ = source29_.minOperands
            d_399___mcc_h100_ = source29_.pushes
            d_400___mcc_h101_ = source29_.pops
            return c
        elif source29_.is_StackOp:
            d_401___mcc_h108_ = source29_.name
            d_402___mcc_h109_ = source29_.opcode
            d_403___mcc_h110_ = source29_.minCapacity
            d_404___mcc_h111_ = source29_.minOperands
            d_405___mcc_h112_ = source29_.pushes
            d_406___mcc_h113_ = source29_.pops
            d_407_opcode_ = d_402___mcc_h109_
            if ((EVMConstants.default__.PUSH0) <= (d_407_opcode_)) and ((d_407_opcode_) <= (EVMConstants.default__.PUSH32)):
                source30_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source30_.is_None:
                    def lambda8_(d_409_pos_):
                        return (d_409_pos_) - (1)

                    d_408_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda8_)
                    return WeakPre.Cond_StCond(d_408_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_410___mcc_h144_ = source30_.v
                    d_411_i_ = d_410___mcc_h144_
                    d_412_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_413___v132_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_411_i_)) == ((d_412_argVal_).Extract()):
                        d_414_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_411_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_411_i_) + (1)::]))
                        if (len(d_414_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda9_(d_416_pos_):
                                return (d_416_pos_) - (1)

                            d_415_shiftByMinusOne_ = MiscTypes.default__.Map(d_414_filtered_, lambda9_)
                            return WeakPre.Cond_StCond(d_415_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_411_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_411_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_407_opcode_)) and ((d_407_opcode_) <= (EVMConstants.default__.DUP16)):
                source31_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source31_.is_None:
                    def lambda10_(d_418_pos_):
                        return (d_418_pos_) - (1)

                    d_417_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda10_)
                    return WeakPre.Cond_StCond(d_417_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_419___mcc_h145_ = source31_.v
                    d_420_index0_ = d_419___mcc_h145_
                    source32_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_407_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source32_.is_None:
                        def lambda11_(d_422_opcode_):
                            def lambda12_(d_423_pos_):
                                return ((d_422_opcode_) - (EVMConstants.default__.DUP1) if (d_423_pos_) == (0) else (d_423_pos_) - (1))

                            return lambda12_

                        d_421_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda11_(d_407_opcode_))
                        return WeakPre.Cond_StCond(d_421_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_424___mcc_h146_ = source32_.v
                        d_425_index_ = d_424___mcc_h146_
                        if ((c).TrackedValAt(d_420_index0_)) == ((c).TrackedValAt(d_425_index_)):
                            d_426_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_420_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_420_index0_) + (1)::]))
                            def lambda13_(d_428_pos_):
                                return (d_428_pos_) - (1)

                            d_427_shiftByMinusOne_ = MiscTypes.default__.Map(d_426_filtered_, lambda13_)
                            return WeakPre.Cond_StCond(d_427_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_420_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_420_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_407_opcode_)) and ((d_407_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_429_k_ = ((d_407_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda14_(d_431_k_):
                    def lambda15_(d_432_pos_):
                        return (d_431_k_ if (d_432_pos_) == (0) else (0 if (d_432_pos_) == (d_431_k_) else d_432_pos_))

                    return lambda15_

                d_430_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda14_(d_429_k_))
                return WeakPre.Cond_StCond(d_430_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda16_(d_434_i_):
                    return (d_434_i_) + (1)

                d_433_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                return WeakPre.Cond_StCond(d_433_shiftByOne_, (c).TrackedVals())
        elif source29_.is_LogOp:
            d_435___mcc_h120_ = source29_.name
            d_436___mcc_h121_ = source29_.opcode
            d_437___mcc_h122_ = source29_.minCapacity
            d_438___mcc_h123_ = source29_.minOperands
            d_439___mcc_h124_ = source29_.pushes
            d_440___mcc_h125_ = source29_.pops
            return c
        elif True:
            d_441___mcc_h132_ = source29_.name
            d_442___mcc_h133_ = source29_.opcode
            d_443___mcc_h134_ = source29_.minCapacity
            d_444___mcc_h135_ = source29_.minOperands
            d_445___mcc_h136_ = source29_.pushes
            d_446___mcc_h137_ = source29_.pops
            return c


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

