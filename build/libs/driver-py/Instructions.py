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
        d_154_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_155___v134_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_154_pad_) + (xc))).Extract()


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
            d_156_k_: int = forall_var_2_
            return not (((0) <= (d_156_k_)) and ((d_156_k_) < (len((self).arg)))) or (Hex.default__.IsHex(((self).arg)[d_156_k_]))

        return ((((self).op).opcode) == (EVMConstants.default__.INVALID)) or ((not (((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32))) or (((len((self).arg)) == ((2) * ((((self).op).opcode) - (EVMConstants.default__.PUSH0)))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).arg)), True, lambda2_)))) and (not (not(((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32)))) or ((len((self).arg)) == (0))))

    def ToString(self):
        d_157_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_157_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_157_x_) if (len(d_157_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

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
        source27_ = (self).op
        if source27_.is_ArithOp:
            d_158___mcc_h0_ = source27_.name
            d_159___mcc_h1_ = source27_.opcode
            d_160___mcc_h2_ = source27_.minCapacity
            d_161___mcc_h3_ = source27_.minOperands
            d_162___mcc_h4_ = source27_.pushes
            d_163___mcc_h5_ = source27_.pops
            d_164_pops_ = d_163___mcc_h5_
            d_165_pushes_ = d_162___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source27_.is_CompOp:
            d_166___mcc_h6_ = source27_.name
            d_167___mcc_h7_ = source27_.opcode
            d_168___mcc_h8_ = source27_.minCapacity
            d_169___mcc_h9_ = source27_.minOperands
            d_170___mcc_h10_ = source27_.pushes
            d_171___mcc_h11_ = source27_.pops
            d_172_pops_ = d_171___mcc_h11_
            d_173_pushes_ = d_170___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_172_pops_)) - (d_173_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source27_.is_BitwiseOp:
            d_174___mcc_h12_ = source27_.name
            d_175___mcc_h13_ = source27_.opcode
            d_176___mcc_h14_ = source27_.minCapacity
            d_177___mcc_h15_ = source27_.minOperands
            d_178___mcc_h16_ = source27_.pushes
            d_179___mcc_h17_ = source27_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source27_.is_KeccakOp:
            d_180___mcc_h18_ = source27_.name
            d_181___mcc_h19_ = source27_.opcode
            d_182___mcc_h20_ = source27_.minCapacity
            d_183___mcc_h21_ = source27_.minOperands
            d_184___mcc_h22_ = source27_.pushes
            d_185___mcc_h23_ = source27_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source27_.is_EnvOp:
            d_186___mcc_h24_ = source27_.name
            d_187___mcc_h25_ = source27_.opcode
            d_188___mcc_h26_ = source27_.minCapacity
            d_189___mcc_h27_ = source27_.minOperands
            d_190___mcc_h28_ = source27_.pushes
            d_191___mcc_h29_ = source27_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source27_.is_MemOp:
            d_192___mcc_h30_ = source27_.name
            d_193___mcc_h31_ = source27_.opcode
            d_194___mcc_h32_ = source27_.minCapacity
            d_195___mcc_h33_ = source27_.minOperands
            d_196___mcc_h34_ = source27_.pushes
            d_197___mcc_h35_ = source27_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source27_.is_StorageOp:
            d_198___mcc_h36_ = source27_.name
            d_199___mcc_h37_ = source27_.opcode
            d_200___mcc_h38_ = source27_.minCapacity
            d_201___mcc_h39_ = source27_.minOperands
            d_202___mcc_h40_ = source27_.pushes
            d_203___mcc_h41_ = source27_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source27_.is_JumpOp:
            d_204___mcc_h42_ = source27_.name
            d_205___mcc_h43_ = source27_.opcode
            d_206___mcc_h44_ = source27_.minCapacity
            d_207___mcc_h45_ = source27_.minOperands
            d_208___mcc_h46_ = source27_.pushes
            d_209___mcc_h47_ = source27_.pops
            d_210_opcode_ = d_205___mcc_h43_
            if (d_210_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_210_opcode_)) and ((d_210_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_211_k_ = ((d_210_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_211_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source27_.is_RunOp:
            d_212___mcc_h48_ = source27_.name
            d_213___mcc_h49_ = source27_.opcode
            d_214___mcc_h50_ = source27_.minCapacity
            d_215___mcc_h51_ = source27_.minOperands
            d_216___mcc_h52_ = source27_.pushes
            d_217___mcc_h53_ = source27_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source27_.is_StackOp:
            d_218___mcc_h54_ = source27_.name
            d_219___mcc_h55_ = source27_.opcode
            d_220___mcc_h56_ = source27_.minCapacity
            d_221___mcc_h57_ = source27_.minOperands
            d_222___mcc_h58_ = source27_.pushes
            d_223___mcc_h59_ = source27_.pops
            d_224_opcode_ = d_219___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_224_opcode_)) and ((d_224_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_224_opcode_)) and ((d_224_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_224_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_224_opcode_)) and ((d_224_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_225_k_ = ((d_224_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_225_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_225_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source27_.is_LogOp:
            d_226___mcc_h60_ = source27_.name
            d_227___mcc_h61_ = source27_.opcode
            d_228___mcc_h62_ = source27_.minCapacity
            d_229___mcc_h63_ = source27_.minOperands
            d_230___mcc_h64_ = source27_.pushes
            d_231___mcc_h65_ = source27_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif True:
            d_232___mcc_h66_ = source27_.name
            d_233___mcc_h67_ = source27_.opcode
            d_234___mcc_h68_ = source27_.minCapacity
            d_235___mcc_h69_ = source27_.minOperands
            d_236___mcc_h70_ = source27_.pushes
            d_237___mcc_h71_ = source27_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))

    def NextState(self, s, cond):
        source28_ = (self).op
        if source28_.is_ArithOp:
            d_238___mcc_h0_ = source28_.name
            d_239___mcc_h1_ = source28_.opcode
            d_240___mcc_h2_ = source28_.minCapacity
            d_241___mcc_h3_ = source28_.minOperands
            d_242___mcc_h4_ = source28_.pushes
            d_243___mcc_h5_ = source28_.pops
            d_244_pops_ = d_243___mcc_h5_
            d_245_pushes_ = d_242___mcc_h4_
            if (((s).Size()) >= (d_244_pops_)) and (not(cond)):
                return (((s).PopN(d_244_pops_)).PushNRandom(d_245_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source28_.is_CompOp:
            d_246___mcc_h6_ = source28_.name
            d_247___mcc_h7_ = source28_.opcode
            d_248___mcc_h8_ = source28_.minCapacity
            d_249___mcc_h9_ = source28_.minOperands
            d_250___mcc_h10_ = source28_.pushes
            d_251___mcc_h11_ = source28_.pops
            d_252_pops_ = d_251___mcc_h11_
            d_253_pushes_ = d_250___mcc_h10_
            if (((s).Size()) >= (d_252_pops_)) and (not(cond)):
                return (((s).PopN(d_252_pops_)).PushNRandom(d_253_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source28_.is_BitwiseOp:
            d_254___mcc_h12_ = source28_.name
            d_255___mcc_h13_ = source28_.opcode
            d_256___mcc_h14_ = source28_.minCapacity
            d_257___mcc_h15_ = source28_.minOperands
            d_258___mcc_h16_ = source28_.pushes
            d_259___mcc_h17_ = source28_.pops
            d_260_pops_ = d_259___mcc_h17_
            d_261_pushes_ = d_258___mcc_h16_
            if (((s).Size()) >= (d_260_pops_)) and (not(cond)):
                return (((s).PopN(d_260_pops_)).PushNRandom(d_261_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source28_.is_KeccakOp:
            d_262___mcc_h18_ = source28_.name
            d_263___mcc_h19_ = source28_.opcode
            d_264___mcc_h20_ = source28_.minCapacity
            d_265___mcc_h21_ = source28_.minOperands
            d_266___mcc_h22_ = source28_.pushes
            d_267___mcc_h23_ = source28_.pops
            d_268_pops_ = d_267___mcc_h23_
            d_269_pushes_ = d_266___mcc_h22_
            if (((s).Size()) >= (2)) and (not(cond)):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source28_.is_EnvOp:
            d_270___mcc_h24_ = source28_.name
            d_271___mcc_h25_ = source28_.opcode
            d_272___mcc_h26_ = source28_.minCapacity
            d_273___mcc_h27_ = source28_.minOperands
            d_274___mcc_h28_ = source28_.pushes
            d_275___mcc_h29_ = source28_.pops
            d_276_pops_ = d_275___mcc_h29_
            d_277_pushes_ = d_274___mcc_h28_
            if (((s).Size()) >= (d_276_pops_)) and (not(cond)):
                return (((s).PopN(d_276_pops_)).PushNRandom(d_277_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        elif source28_.is_MemOp:
            d_278___mcc_h30_ = source28_.name
            d_279___mcc_h31_ = source28_.opcode
            d_280___mcc_h32_ = source28_.minCapacity
            d_281___mcc_h33_ = source28_.minOperands
            d_282___mcc_h34_ = source28_.pushes
            d_283___mcc_h35_ = source28_.pops
            d_284_pops_ = d_283___mcc_h35_
            d_285_pushes_ = d_282___mcc_h34_
            if (((s).Size()) >= (d_284_pops_)) and (not(cond)):
                return (((s).PopN(d_284_pops_)).PushNRandom(d_285_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        elif source28_.is_StorageOp:
            d_286___mcc_h36_ = source28_.name
            d_287___mcc_h37_ = source28_.opcode
            d_288___mcc_h38_ = source28_.minCapacity
            d_289___mcc_h39_ = source28_.minOperands
            d_290___mcc_h40_ = source28_.pushes
            d_291___mcc_h41_ = source28_.pops
            d_292_pops_ = d_291___mcc_h41_
            d_293_pushes_ = d_290___mcc_h40_
            if (((s).Size()) >= (d_292_pops_)) and (not(cond)):
                return (((s).PopN(d_292_pops_)).PushNRandom(d_293_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        elif source28_.is_JumpOp:
            d_294___mcc_h42_ = source28_.name
            d_295___mcc_h43_ = source28_.opcode
            d_296___mcc_h44_ = source28_.minCapacity
            d_297___mcc_h45_ = source28_.minOperands
            d_298___mcc_h46_ = source28_.pushes
            d_299___mcc_h47_ = source28_.pops
            d_300_pops_ = d_299___mcc_h47_
            d_301_pushes_ = d_298___mcc_h46_
            d_302_opcode_ = d_295___mcc_h43_
            if (d_302_opcode_) == (EVMConstants.default__.JUMPDEST):
                if not(cond):
                    return (s).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPDEST/exit true")))
            elif (d_302_opcode_) == (EVMConstants.default__.JUMP):
                if (((s).Size()) >= (1)) and (cond):
                    source29_ = (s).Peek(0)
                    if source29_.is_Value:
                        d_303___mcc_h72_ = source29_.v
                        d_304_v_ = d_303___mcc_h72_
                        return ((s).Pop()).Goto(d_304_v_)
                    elif True:
                        d_305___mcc_h73_ = source29_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_302_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source30_ = (s).Peek(0)
                    if source30_.is_Value:
                        d_306___mcc_h74_ = source30_.v
                        d_307_v_ = d_306___mcc_h74_
                        if cond:
                            return ((s).PopN(2)).Goto(d_307_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_308___mcc_h75_ = source30_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source28_.is_RunOp:
            d_309___mcc_h48_ = source28_.name
            d_310___mcc_h49_ = source28_.opcode
            d_311___mcc_h50_ = source28_.minCapacity
            d_312___mcc_h51_ = source28_.minOperands
            d_313___mcc_h52_ = source28_.pushes
            d_314___mcc_h53_ = source28_.pops
            d_315_pops_ = d_314___mcc_h53_
            d_316_pushes_ = d_313___mcc_h52_
            if not(cond):
                return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RunOp error")))
        elif source28_.is_StackOp:
            d_317___mcc_h54_ = source28_.name
            d_318___mcc_h55_ = source28_.opcode
            d_319___mcc_h56_ = source28_.minCapacity
            d_320___mcc_h57_ = source28_.minOperands
            d_321___mcc_h58_ = source28_.pushes
            d_322___mcc_h59_ = source28_.pops
            d_323_pops_ = d_322___mcc_h59_
            d_324_pushes_ = d_321___mcc_h58_
            d_325_opcode_ = d_318___mcc_h55_
            if (((d_325_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1))) and (not(cond)):
                return ((s).Pop()).Skip(1)
            elif (((EVMConstants.default__.PUSH0) <= (d_325_opcode_)) and ((d_325_opcode_) <= (EVMConstants.default__.PUSH32))) and (not(cond)):
                return ((s).Push(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))).Skip((1) + ((d_325_opcode_) - (EVMConstants.default__.PUSH0)))
            elif ((((EVMConstants.default__.DUP1) <= (d_325_opcode_)) and ((d_325_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_325_opcode_) - (EVMConstants.default__.DUP1)) + (1)))) and (not(cond)):
                return ((s).Dup(((d_325_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif ((((EVMConstants.default__.SWAP1) <= (d_325_opcode_)) and ((d_325_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_325_opcode_) - (EVMConstants.default__.SWAP1)) + (1)))) and (not(cond)):
                return ((s).Swap(((d_325_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        elif source28_.is_LogOp:
            d_326___mcc_h60_ = source28_.name
            d_327___mcc_h61_ = source28_.opcode
            d_328___mcc_h62_ = source28_.minCapacity
            d_329___mcc_h63_ = source28_.minOperands
            d_330___mcc_h64_ = source28_.pushes
            d_331___mcc_h65_ = source28_.pops
            d_332_pops_ = d_331___mcc_h65_
            d_333_pushes_ = d_330___mcc_h64_
            if (((s).Size()) >= (d_332_pops_)) and (not(cond)):
                return ((s).PopN(d_332_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        elif True:
            d_334___mcc_h66_ = source28_.name
            d_335___mcc_h67_ = source28_.opcode
            d_336___mcc_h68_ = source28_.minCapacity
            d_337___mcc_h69_ = source28_.minOperands
            d_338___mcc_h70_ = source28_.pushes
            d_339___mcc_h71_ = source28_.pops
            d_340_pops_ = d_339___mcc_h71_
            d_341_pushes_ = d_338___mcc_h70_
            if (((s).Size()) >= (d_340_pops_)) and (not(cond)):
                return (((s).PopN(d_340_pops_)).PushNRandom(d_341_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source31_ = (self).op
        if source31_.is_ArithOp:
            d_342___mcc_h0_ = source31_.name
            d_343___mcc_h1_ = source31_.opcode
            d_344___mcc_h2_ = source31_.minCapacity
            d_345___mcc_h3_ = source31_.minOperands
            d_346___mcc_h4_ = source31_.pushes
            d_347___mcc_h5_ = source31_.pops
            d_348_pops_ = d_347___mcc_h5_
            d_349_pushes_ = d_346___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda3_(d_351_pos_):
                    return (d_351_pos_) + (1)

                d_350_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda3_)
                return WeakPre.Cond_StCond(d_350_shiftByOne_, (c).TrackedVals())
        elif source31_.is_CompOp:
            d_352___mcc_h12_ = source31_.name
            d_353___mcc_h13_ = source31_.opcode
            d_354___mcc_h14_ = source31_.minCapacity
            d_355___mcc_h15_ = source31_.minOperands
            d_356___mcc_h16_ = source31_.pushes
            d_357___mcc_h17_ = source31_.pops
            d_358_pops_ = d_357___mcc_h17_
            d_359_pushes_ = d_356___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda4_(d_361_pops_, d_362_pushes_):
                    def lambda5_(d_363_pos_):
                        return ((d_363_pos_) + (d_361_pops_)) - (d_362_pushes_)

                    return lambda5_

                d_360_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda4_(d_358_pops_, d_359_pushes_))
                return WeakPre.Cond_StCond(d_360_shiftBy_, (c).TrackedVals())
        elif source31_.is_BitwiseOp:
            d_364___mcc_h24_ = source31_.name
            d_365___mcc_h25_ = source31_.opcode
            d_366___mcc_h26_ = source31_.minCapacity
            d_367___mcc_h27_ = source31_.minOperands
            d_368___mcc_h28_ = source31_.pushes
            d_369___mcc_h29_ = source31_.pops
            return c
        elif source31_.is_KeccakOp:
            d_370___mcc_h36_ = source31_.name
            d_371___mcc_h37_ = source31_.opcode
            d_372___mcc_h38_ = source31_.minCapacity
            d_373___mcc_h39_ = source31_.minOperands
            d_374___mcc_h40_ = source31_.pushes
            d_375___mcc_h41_ = source31_.pops
            return c
        elif source31_.is_EnvOp:
            d_376___mcc_h48_ = source31_.name
            d_377___mcc_h49_ = source31_.opcode
            d_378___mcc_h50_ = source31_.minCapacity
            d_379___mcc_h51_ = source31_.minOperands
            d_380___mcc_h52_ = source31_.pushes
            d_381___mcc_h53_ = source31_.pops
            return c
        elif source31_.is_MemOp:
            d_382___mcc_h60_ = source31_.name
            d_383___mcc_h61_ = source31_.opcode
            d_384___mcc_h62_ = source31_.minCapacity
            d_385___mcc_h63_ = source31_.minOperands
            d_386___mcc_h64_ = source31_.pushes
            d_387___mcc_h65_ = source31_.pops
            return c
        elif source31_.is_StorageOp:
            d_388___mcc_h72_ = source31_.name
            d_389___mcc_h73_ = source31_.opcode
            d_390___mcc_h74_ = source31_.minCapacity
            d_391___mcc_h75_ = source31_.minOperands
            d_392___mcc_h76_ = source31_.pushes
            d_393___mcc_h77_ = source31_.pops
            return c
        elif source31_.is_JumpOp:
            d_394___mcc_h84_ = source31_.name
            d_395___mcc_h85_ = source31_.opcode
            d_396___mcc_h86_ = source31_.minCapacity
            d_397___mcc_h87_ = source31_.minOperands
            d_398___mcc_h88_ = source31_.pushes
            d_399___mcc_h89_ = source31_.pops
            d_400_opcode_ = d_395___mcc_h85_
            if (d_400_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_400_opcode_)) and ((d_400_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_401_k_ = ((d_400_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda6_(d_403_k_):
                    def lambda7_(d_404_pos_):
                        return (d_404_pos_) + (d_403_k_)

                    return lambda7_

                d_402_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_(d_401_k_))
                return WeakPre.Cond_StCond(d_402_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source31_.is_RunOp:
            d_405___mcc_h96_ = source31_.name
            d_406___mcc_h97_ = source31_.opcode
            d_407___mcc_h98_ = source31_.minCapacity
            d_408___mcc_h99_ = source31_.minOperands
            d_409___mcc_h100_ = source31_.pushes
            d_410___mcc_h101_ = source31_.pops
            return c
        elif source31_.is_StackOp:
            d_411___mcc_h108_ = source31_.name
            d_412___mcc_h109_ = source31_.opcode
            d_413___mcc_h110_ = source31_.minCapacity
            d_414___mcc_h111_ = source31_.minOperands
            d_415___mcc_h112_ = source31_.pushes
            d_416___mcc_h113_ = source31_.pops
            d_417_opcode_ = d_412___mcc_h109_
            if ((EVMConstants.default__.PUSH0) <= (d_417_opcode_)) and ((d_417_opcode_) <= (EVMConstants.default__.PUSH32)):
                source32_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source32_.is_None:
                    def lambda8_(d_419_pos_):
                        return (d_419_pos_) - (1)

                    d_418_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda8_)
                    return WeakPre.Cond_StCond(d_418_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_420___mcc_h144_ = source32_.v
                    d_421_i_ = d_420___mcc_h144_
                    d_422_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_423___v132_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_421_i_)) == ((d_422_argVal_).Extract()):
                        d_424_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_421_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_421_i_) + (1)::]))
                        if (len(d_424_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda9_(d_426_pos_):
                                return (d_426_pos_) - (1)

                            d_425_shiftByMinusOne_ = MiscTypes.default__.Map(d_424_filtered_, lambda9_)
                            return WeakPre.Cond_StCond(d_425_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_421_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_421_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_417_opcode_)) and ((d_417_opcode_) <= (EVMConstants.default__.DUP16)):
                source33_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source33_.is_None:
                    def lambda10_(d_428_pos_):
                        return (d_428_pos_) - (1)

                    d_427_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda10_)
                    return WeakPre.Cond_StCond(d_427_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_429___mcc_h145_ = source33_.v
                    d_430_index0_ = d_429___mcc_h145_
                    source34_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_417_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source34_.is_None:
                        def lambda11_(d_432_opcode_):
                            def lambda12_(d_433_pos_):
                                return ((d_432_opcode_) - (EVMConstants.default__.DUP1) if (d_433_pos_) == (0) else (d_433_pos_) - (1))

                            return lambda12_

                        d_431_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda11_(d_417_opcode_))
                        return WeakPre.Cond_StCond(d_431_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_434___mcc_h146_ = source34_.v
                        d_435_index_ = d_434___mcc_h146_
                        if ((c).TrackedValAt(d_430_index0_)) == ((c).TrackedValAt(d_435_index_)):
                            d_436_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_430_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_430_index0_) + (1)::]))
                            def lambda13_(d_438_pos_):
                                return (d_438_pos_) - (1)

                            d_437_shiftByMinusOne_ = MiscTypes.default__.Map(d_436_filtered_, lambda13_)
                            return WeakPre.Cond_StCond(d_437_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_430_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_430_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_417_opcode_)) and ((d_417_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_439_k_ = ((d_417_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda14_(d_441_k_):
                    def lambda15_(d_442_pos_):
                        return (d_441_k_ if (d_442_pos_) == (0) else (0 if (d_442_pos_) == (d_441_k_) else d_442_pos_))

                    return lambda15_

                d_440_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda14_(d_439_k_))
                return WeakPre.Cond_StCond(d_440_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda16_(d_444_i_):
                    return (d_444_i_) + (1)

                d_443_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                return WeakPre.Cond_StCond(d_443_shiftByOne_, (c).TrackedVals())
        elif source31_.is_LogOp:
            d_445___mcc_h120_ = source31_.name
            d_446___mcc_h121_ = source31_.opcode
            d_447___mcc_h122_ = source31_.minCapacity
            d_448___mcc_h123_ = source31_.minOperands
            d_449___mcc_h124_ = source31_.pushes
            d_450___mcc_h125_ = source31_.pops
            return c
        elif True:
            d_451___mcc_h132_ = source31_.name
            d_452___mcc_h133_ = source31_.opcode
            d_453___mcc_h134_ = source31_.minCapacity
            d_454___mcc_h135_ = source31_.minOperands
            d_455___mcc_h136_ = source31_.pushes
            d_456___mcc_h137_ = source31_.pops
            return c


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

