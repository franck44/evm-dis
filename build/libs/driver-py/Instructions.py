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
        d_172_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_173___v134_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_172_pad_) + (xc))).Extract()


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
            d_174_k_: int = forall_var_2_
            return not (((0) <= (d_174_k_)) and ((d_174_k_) < (len((self).arg)))) or (Hex.default__.IsHex(((self).arg)[d_174_k_]))

        return ((((self).op).opcode) == (EVMConstants.default__.INVALID)) or ((not (((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32))) or (((len((self).arg)) == ((2) * ((((self).op).opcode) - (EVMConstants.default__.PUSH0)))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).arg)), True, lambda2_)))) and (not (not(((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32)))) or ((len((self).arg)) == (0))))

    def ToString(self):
        d_175_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_175_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_175_x_) if (len(d_175_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

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
        source32_ = (self).op
        if source32_.is_ArithOp:
            d_176___mcc_h0_ = source32_.name
            d_177___mcc_h1_ = source32_.opcode
            d_178___mcc_h2_ = source32_.minCapacity
            d_179___mcc_h3_ = source32_.minOperands
            d_180___mcc_h4_ = source32_.pushes
            d_181___mcc_h5_ = source32_.pops
            d_182_pops_ = d_181___mcc_h5_
            d_183_pushes_ = d_180___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source32_.is_CompOp:
            d_184___mcc_h6_ = source32_.name
            d_185___mcc_h7_ = source32_.opcode
            d_186___mcc_h8_ = source32_.minCapacity
            d_187___mcc_h9_ = source32_.minOperands
            d_188___mcc_h10_ = source32_.pushes
            d_189___mcc_h11_ = source32_.pops
            d_190_pops_ = d_189___mcc_h11_
            d_191_pushes_ = d_188___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_190_pops_)) - (d_191_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source32_.is_BitwiseOp:
            d_192___mcc_h12_ = source32_.name
            d_193___mcc_h13_ = source32_.opcode
            d_194___mcc_h14_ = source32_.minCapacity
            d_195___mcc_h15_ = source32_.minOperands
            d_196___mcc_h16_ = source32_.pushes
            d_197___mcc_h17_ = source32_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source32_.is_KeccakOp:
            d_198___mcc_h18_ = source32_.name
            d_199___mcc_h19_ = source32_.opcode
            d_200___mcc_h20_ = source32_.minCapacity
            d_201___mcc_h21_ = source32_.minOperands
            d_202___mcc_h22_ = source32_.pushes
            d_203___mcc_h23_ = source32_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source32_.is_EnvOp:
            d_204___mcc_h24_ = source32_.name
            d_205___mcc_h25_ = source32_.opcode
            d_206___mcc_h26_ = source32_.minCapacity
            d_207___mcc_h27_ = source32_.minOperands
            d_208___mcc_h28_ = source32_.pushes
            d_209___mcc_h29_ = source32_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source32_.is_MemOp:
            d_210___mcc_h30_ = source32_.name
            d_211___mcc_h31_ = source32_.opcode
            d_212___mcc_h32_ = source32_.minCapacity
            d_213___mcc_h33_ = source32_.minOperands
            d_214___mcc_h34_ = source32_.pushes
            d_215___mcc_h35_ = source32_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source32_.is_StorageOp:
            d_216___mcc_h36_ = source32_.name
            d_217___mcc_h37_ = source32_.opcode
            d_218___mcc_h38_ = source32_.minCapacity
            d_219___mcc_h39_ = source32_.minOperands
            d_220___mcc_h40_ = source32_.pushes
            d_221___mcc_h41_ = source32_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source32_.is_JumpOp:
            d_222___mcc_h42_ = source32_.name
            d_223___mcc_h43_ = source32_.opcode
            d_224___mcc_h44_ = source32_.minCapacity
            d_225___mcc_h45_ = source32_.minOperands
            d_226___mcc_h46_ = source32_.pushes
            d_227___mcc_h47_ = source32_.pops
            d_228_opcode_ = d_223___mcc_h43_
            if (d_228_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_228_opcode_)) and ((d_228_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_229_k_ = ((d_228_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_229_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source32_.is_RunOp:
            d_230___mcc_h48_ = source32_.name
            d_231___mcc_h49_ = source32_.opcode
            d_232___mcc_h50_ = source32_.minCapacity
            d_233___mcc_h51_ = source32_.minOperands
            d_234___mcc_h52_ = source32_.pushes
            d_235___mcc_h53_ = source32_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source32_.is_StackOp:
            d_236___mcc_h54_ = source32_.name
            d_237___mcc_h55_ = source32_.opcode
            d_238___mcc_h56_ = source32_.minCapacity
            d_239___mcc_h57_ = source32_.minOperands
            d_240___mcc_h58_ = source32_.pushes
            d_241___mcc_h59_ = source32_.pops
            d_242_opcode_ = d_237___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_242_opcode_)) and ((d_242_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_242_opcode_)) and ((d_242_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_242_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_242_opcode_)) and ((d_242_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_243_k_ = ((d_242_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_243_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_243_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source32_.is_LogOp:
            d_244___mcc_h60_ = source32_.name
            d_245___mcc_h61_ = source32_.opcode
            d_246___mcc_h62_ = source32_.minCapacity
            d_247___mcc_h63_ = source32_.minOperands
            d_248___mcc_h64_ = source32_.pushes
            d_249___mcc_h65_ = source32_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif True:
            d_250___mcc_h66_ = source32_.name
            d_251___mcc_h67_ = source32_.opcode
            d_252___mcc_h68_ = source32_.minCapacity
            d_253___mcc_h69_ = source32_.minOperands
            d_254___mcc_h70_ = source32_.pushes
            d_255___mcc_h71_ = source32_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))

    def NextState(self, s, cond):
        source33_ = (self).op
        if source33_.is_ArithOp:
            d_256___mcc_h0_ = source33_.name
            d_257___mcc_h1_ = source33_.opcode
            d_258___mcc_h2_ = source33_.minCapacity
            d_259___mcc_h3_ = source33_.minOperands
            d_260___mcc_h4_ = source33_.pushes
            d_261___mcc_h5_ = source33_.pops
            d_262_pops_ = d_261___mcc_h5_
            d_263_pushes_ = d_260___mcc_h4_
            if (((s).Size()) >= (d_262_pops_)) and (not(cond)):
                return (((s).PopN(d_262_pops_)).PushNRandom(d_263_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source33_.is_CompOp:
            d_264___mcc_h6_ = source33_.name
            d_265___mcc_h7_ = source33_.opcode
            d_266___mcc_h8_ = source33_.minCapacity
            d_267___mcc_h9_ = source33_.minOperands
            d_268___mcc_h10_ = source33_.pushes
            d_269___mcc_h11_ = source33_.pops
            d_270_pops_ = d_269___mcc_h11_
            d_271_pushes_ = d_268___mcc_h10_
            if (((s).Size()) >= (d_270_pops_)) and (not(cond)):
                return (((s).PopN(d_270_pops_)).PushNRandom(d_271_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source33_.is_BitwiseOp:
            d_272___mcc_h12_ = source33_.name
            d_273___mcc_h13_ = source33_.opcode
            d_274___mcc_h14_ = source33_.minCapacity
            d_275___mcc_h15_ = source33_.minOperands
            d_276___mcc_h16_ = source33_.pushes
            d_277___mcc_h17_ = source33_.pops
            d_278_pops_ = d_277___mcc_h17_
            d_279_pushes_ = d_276___mcc_h16_
            if (((s).Size()) >= (d_278_pops_)) and (not(cond)):
                return (((s).PopN(d_278_pops_)).PushNRandom(d_279_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source33_.is_KeccakOp:
            d_280___mcc_h18_ = source33_.name
            d_281___mcc_h19_ = source33_.opcode
            d_282___mcc_h20_ = source33_.minCapacity
            d_283___mcc_h21_ = source33_.minOperands
            d_284___mcc_h22_ = source33_.pushes
            d_285___mcc_h23_ = source33_.pops
            d_286_pops_ = d_285___mcc_h23_
            d_287_pushes_ = d_284___mcc_h22_
            if (((s).Size()) >= (2)) and (not(cond)):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source33_.is_EnvOp:
            d_288___mcc_h24_ = source33_.name
            d_289___mcc_h25_ = source33_.opcode
            d_290___mcc_h26_ = source33_.minCapacity
            d_291___mcc_h27_ = source33_.minOperands
            d_292___mcc_h28_ = source33_.pushes
            d_293___mcc_h29_ = source33_.pops
            d_294_pops_ = d_293___mcc_h29_
            d_295_pushes_ = d_292___mcc_h28_
            if (((s).Size()) >= (d_294_pops_)) and (not(cond)):
                return (((s).PopN(d_294_pops_)).PushNRandom(d_295_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        elif source33_.is_MemOp:
            d_296___mcc_h30_ = source33_.name
            d_297___mcc_h31_ = source33_.opcode
            d_298___mcc_h32_ = source33_.minCapacity
            d_299___mcc_h33_ = source33_.minOperands
            d_300___mcc_h34_ = source33_.pushes
            d_301___mcc_h35_ = source33_.pops
            d_302_pops_ = d_301___mcc_h35_
            d_303_pushes_ = d_300___mcc_h34_
            if (((s).Size()) >= (d_302_pops_)) and (not(cond)):
                return (((s).PopN(d_302_pops_)).PushNRandom(d_303_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        elif source33_.is_StorageOp:
            d_304___mcc_h36_ = source33_.name
            d_305___mcc_h37_ = source33_.opcode
            d_306___mcc_h38_ = source33_.minCapacity
            d_307___mcc_h39_ = source33_.minOperands
            d_308___mcc_h40_ = source33_.pushes
            d_309___mcc_h41_ = source33_.pops
            d_310_pops_ = d_309___mcc_h41_
            d_311_pushes_ = d_308___mcc_h40_
            if (((s).Size()) >= (d_310_pops_)) and (not(cond)):
                return (((s).PopN(d_310_pops_)).PushNRandom(d_311_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        elif source33_.is_JumpOp:
            d_312___mcc_h42_ = source33_.name
            d_313___mcc_h43_ = source33_.opcode
            d_314___mcc_h44_ = source33_.minCapacity
            d_315___mcc_h45_ = source33_.minOperands
            d_316___mcc_h46_ = source33_.pushes
            d_317___mcc_h47_ = source33_.pops
            d_318_pops_ = d_317___mcc_h47_
            d_319_pushes_ = d_316___mcc_h46_
            d_320_opcode_ = d_313___mcc_h43_
            if (d_320_opcode_) == (EVMConstants.default__.JUMPDEST):
                if not(cond):
                    return (s).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPDEST/exit true")))
            elif (d_320_opcode_) == (EVMConstants.default__.JUMP):
                if (((s).Size()) >= (1)) and (cond):
                    source34_ = (s).Peek(0)
                    if source34_.is_Value:
                        d_321___mcc_h72_ = source34_.v
                        d_322_v_ = d_321___mcc_h72_
                        return ((s).Pop()).Goto(d_322_v_)
                    elif True:
                        d_323___mcc_h73_ = source34_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_320_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source35_ = (s).Peek(0)
                    if source35_.is_Value:
                        d_324___mcc_h74_ = source35_.v
                        d_325_v_ = d_324___mcc_h74_
                        if cond:
                            return ((s).PopN(2)).Goto(d_325_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_326___mcc_h75_ = source35_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source33_.is_RunOp:
            d_327___mcc_h48_ = source33_.name
            d_328___mcc_h49_ = source33_.opcode
            d_329___mcc_h50_ = source33_.minCapacity
            d_330___mcc_h51_ = source33_.minOperands
            d_331___mcc_h52_ = source33_.pushes
            d_332___mcc_h53_ = source33_.pops
            d_333_pops_ = d_332___mcc_h53_
            d_334_pushes_ = d_331___mcc_h52_
            if not(cond):
                return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RunOp error")))
        elif source33_.is_StackOp:
            d_335___mcc_h54_ = source33_.name
            d_336___mcc_h55_ = source33_.opcode
            d_337___mcc_h56_ = source33_.minCapacity
            d_338___mcc_h57_ = source33_.minOperands
            d_339___mcc_h58_ = source33_.pushes
            d_340___mcc_h59_ = source33_.pops
            d_341_pops_ = d_340___mcc_h59_
            d_342_pushes_ = d_339___mcc_h58_
            d_343_opcode_ = d_336___mcc_h55_
            if (((d_343_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1))) and (not(cond)):
                return ((s).Pop()).Skip(1)
            elif (((EVMConstants.default__.PUSH0) <= (d_343_opcode_)) and ((d_343_opcode_) <= (EVMConstants.default__.PUSH32))) and (not(cond)):
                return ((s).Push(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))).Skip((1) + ((d_343_opcode_) - (EVMConstants.default__.PUSH0)))
            elif ((((EVMConstants.default__.DUP1) <= (d_343_opcode_)) and ((d_343_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_343_opcode_) - (EVMConstants.default__.DUP1)) + (1)))) and (not(cond)):
                return ((s).Dup(((d_343_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif ((((EVMConstants.default__.SWAP1) <= (d_343_opcode_)) and ((d_343_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_343_opcode_) - (EVMConstants.default__.SWAP1)) + (1)))) and (not(cond)):
                return ((s).Swap(((d_343_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        elif source33_.is_LogOp:
            d_344___mcc_h60_ = source33_.name
            d_345___mcc_h61_ = source33_.opcode
            d_346___mcc_h62_ = source33_.minCapacity
            d_347___mcc_h63_ = source33_.minOperands
            d_348___mcc_h64_ = source33_.pushes
            d_349___mcc_h65_ = source33_.pops
            d_350_pops_ = d_349___mcc_h65_
            d_351_pushes_ = d_348___mcc_h64_
            if (((s).Size()) >= (d_350_pops_)) and (not(cond)):
                return ((s).PopN(d_350_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        elif True:
            d_352___mcc_h66_ = source33_.name
            d_353___mcc_h67_ = source33_.opcode
            d_354___mcc_h68_ = source33_.minCapacity
            d_355___mcc_h69_ = source33_.minOperands
            d_356___mcc_h70_ = source33_.pushes
            d_357___mcc_h71_ = source33_.pops
            d_358_pops_ = d_357___mcc_h71_
            d_359_pushes_ = d_356___mcc_h70_
            if (((s).Size()) >= (d_358_pops_)) and (not(cond)):
                return (((s).PopN(d_358_pops_)).PushNRandom(d_359_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source36_ = (self).op
        if source36_.is_ArithOp:
            d_360___mcc_h0_ = source36_.name
            d_361___mcc_h1_ = source36_.opcode
            d_362___mcc_h2_ = source36_.minCapacity
            d_363___mcc_h3_ = source36_.minOperands
            d_364___mcc_h4_ = source36_.pushes
            d_365___mcc_h5_ = source36_.pops
            d_366_pops_ = d_365___mcc_h5_
            d_367_pushes_ = d_364___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda3_(d_369_pos_):
                    return (d_369_pos_) + (1)

                d_368_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda3_)
                return WeakPre.Cond_StCond(d_368_shiftByOne_, (c).TrackedVals())
        elif source36_.is_CompOp:
            d_370___mcc_h12_ = source36_.name
            d_371___mcc_h13_ = source36_.opcode
            d_372___mcc_h14_ = source36_.minCapacity
            d_373___mcc_h15_ = source36_.minOperands
            d_374___mcc_h16_ = source36_.pushes
            d_375___mcc_h17_ = source36_.pops
            d_376_pops_ = d_375___mcc_h17_
            d_377_pushes_ = d_374___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda4_(d_379_pops_, d_380_pushes_):
                    def lambda5_(d_381_pos_):
                        return ((d_381_pos_) + (d_379_pops_)) - (d_380_pushes_)

                    return lambda5_

                d_378_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda4_(d_376_pops_, d_377_pushes_))
                return WeakPre.Cond_StCond(d_378_shiftBy_, (c).TrackedVals())
        elif source36_.is_BitwiseOp:
            d_382___mcc_h24_ = source36_.name
            d_383___mcc_h25_ = source36_.opcode
            d_384___mcc_h26_ = source36_.minCapacity
            d_385___mcc_h27_ = source36_.minOperands
            d_386___mcc_h28_ = source36_.pushes
            d_387___mcc_h29_ = source36_.pops
            return c
        elif source36_.is_KeccakOp:
            d_388___mcc_h36_ = source36_.name
            d_389___mcc_h37_ = source36_.opcode
            d_390___mcc_h38_ = source36_.minCapacity
            d_391___mcc_h39_ = source36_.minOperands
            d_392___mcc_h40_ = source36_.pushes
            d_393___mcc_h41_ = source36_.pops
            return c
        elif source36_.is_EnvOp:
            d_394___mcc_h48_ = source36_.name
            d_395___mcc_h49_ = source36_.opcode
            d_396___mcc_h50_ = source36_.minCapacity
            d_397___mcc_h51_ = source36_.minOperands
            d_398___mcc_h52_ = source36_.pushes
            d_399___mcc_h53_ = source36_.pops
            return c
        elif source36_.is_MemOp:
            d_400___mcc_h60_ = source36_.name
            d_401___mcc_h61_ = source36_.opcode
            d_402___mcc_h62_ = source36_.minCapacity
            d_403___mcc_h63_ = source36_.minOperands
            d_404___mcc_h64_ = source36_.pushes
            d_405___mcc_h65_ = source36_.pops
            return c
        elif source36_.is_StorageOp:
            d_406___mcc_h72_ = source36_.name
            d_407___mcc_h73_ = source36_.opcode
            d_408___mcc_h74_ = source36_.minCapacity
            d_409___mcc_h75_ = source36_.minOperands
            d_410___mcc_h76_ = source36_.pushes
            d_411___mcc_h77_ = source36_.pops
            return c
        elif source36_.is_JumpOp:
            d_412___mcc_h84_ = source36_.name
            d_413___mcc_h85_ = source36_.opcode
            d_414___mcc_h86_ = source36_.minCapacity
            d_415___mcc_h87_ = source36_.minOperands
            d_416___mcc_h88_ = source36_.pushes
            d_417___mcc_h89_ = source36_.pops
            d_418_opcode_ = d_413___mcc_h85_
            if (d_418_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_418_opcode_)) and ((d_418_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_419_k_ = ((d_418_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda6_(d_421_k_):
                    def lambda7_(d_422_pos_):
                        return (d_422_pos_) + (d_421_k_)

                    return lambda7_

                d_420_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_(d_419_k_))
                return WeakPre.Cond_StCond(d_420_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source36_.is_RunOp:
            d_423___mcc_h96_ = source36_.name
            d_424___mcc_h97_ = source36_.opcode
            d_425___mcc_h98_ = source36_.minCapacity
            d_426___mcc_h99_ = source36_.minOperands
            d_427___mcc_h100_ = source36_.pushes
            d_428___mcc_h101_ = source36_.pops
            return c
        elif source36_.is_StackOp:
            d_429___mcc_h108_ = source36_.name
            d_430___mcc_h109_ = source36_.opcode
            d_431___mcc_h110_ = source36_.minCapacity
            d_432___mcc_h111_ = source36_.minOperands
            d_433___mcc_h112_ = source36_.pushes
            d_434___mcc_h113_ = source36_.pops
            d_435_opcode_ = d_430___mcc_h109_
            if ((EVMConstants.default__.PUSH0) <= (d_435_opcode_)) and ((d_435_opcode_) <= (EVMConstants.default__.PUSH32)):
                source37_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source37_.is_None:
                    def lambda8_(d_437_pos_):
                        return (d_437_pos_) - (1)

                    d_436_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda8_)
                    return WeakPre.Cond_StCond(d_436_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_438___mcc_h144_ = source37_.v
                    d_439_i_ = d_438___mcc_h144_
                    d_440_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_441___v132_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_439_i_)) == ((d_440_argVal_).Extract()):
                        d_442_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_439_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_439_i_) + (1)::]))
                        if (len(d_442_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda9_(d_444_pos_):
                                return (d_444_pos_) - (1)

                            d_443_shiftByMinusOne_ = MiscTypes.default__.Map(d_442_filtered_, lambda9_)
                            return WeakPre.Cond_StCond(d_443_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_439_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_439_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_435_opcode_)) and ((d_435_opcode_) <= (EVMConstants.default__.DUP16)):
                source38_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source38_.is_None:
                    def lambda10_(d_446_pos_):
                        return (d_446_pos_) - (1)

                    d_445_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda10_)
                    return WeakPre.Cond_StCond(d_445_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_447___mcc_h145_ = source38_.v
                    d_448_index0_ = d_447___mcc_h145_
                    source39_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_435_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source39_.is_None:
                        def lambda11_(d_450_opcode_):
                            def lambda12_(d_451_pos_):
                                return ((d_450_opcode_) - (EVMConstants.default__.DUP1) if (d_451_pos_) == (0) else (d_451_pos_) - (1))

                            return lambda12_

                        d_449_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda11_(d_435_opcode_))
                        return WeakPre.Cond_StCond(d_449_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_452___mcc_h146_ = source39_.v
                        d_453_index_ = d_452___mcc_h146_
                        if ((c).TrackedValAt(d_448_index0_)) == ((c).TrackedValAt(d_453_index_)):
                            d_454_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_448_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_448_index0_) + (1)::]))
                            def lambda13_(d_456_pos_):
                                return (d_456_pos_) - (1)

                            d_455_shiftByMinusOne_ = MiscTypes.default__.Map(d_454_filtered_, lambda13_)
                            return WeakPre.Cond_StCond(d_455_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_448_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_448_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_435_opcode_)) and ((d_435_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_457_k_ = ((d_435_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda14_(d_459_k_):
                    def lambda15_(d_460_pos_):
                        return (d_459_k_ if (d_460_pos_) == (0) else (0 if (d_460_pos_) == (d_459_k_) else d_460_pos_))

                    return lambda15_

                d_458_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda14_(d_457_k_))
                return WeakPre.Cond_StCond(d_458_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda16_(d_462_i_):
                    return (d_462_i_) + (1)

                d_461_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                return WeakPre.Cond_StCond(d_461_shiftByOne_, (c).TrackedVals())
        elif source36_.is_LogOp:
            d_463___mcc_h120_ = source36_.name
            d_464___mcc_h121_ = source36_.opcode
            d_465___mcc_h122_ = source36_.minCapacity
            d_466___mcc_h123_ = source36_.minOperands
            d_467___mcc_h124_ = source36_.pushes
            d_468___mcc_h125_ = source36_.pops
            return c
        elif True:
            d_469___mcc_h132_ = source36_.name
            d_470___mcc_h133_ = source36_.opcode
            d_471___mcc_h134_ = source36_.minCapacity
            d_472___mcc_h135_ = source36_.minOperands
            d_473___mcc_h136_ = source36_.pushes
            d_474___mcc_h137_ = source36_.pops
            return c


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

