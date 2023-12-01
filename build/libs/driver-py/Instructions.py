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
import WeakPre
import State
import EVMToolTips

# Module: Instructions

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetArgValuePush(xc):
        d_183_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_184___v165_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_183_pad_) + (xc))).Extract()

    @staticmethod
    def Colours(i):
        source32_ = (i).op
        if source32_.is_ArithOp:
            d_185___mcc_h0_ = source32_.name
            d_186___mcc_h1_ = source32_.opcode
            d_187___mcc_h2_ = source32_.minCapacity
            d_188___mcc_h3_ = source32_.minOperands
            d_189___mcc_h4_ = source32_.pushes
            d_190___mcc_h5_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#316152")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#c6eb76")))
        elif source32_.is_CompOp:
            d_191___mcc_h6_ = source32_.name
            d_192___mcc_h7_ = source32_.opcode
            d_193___mcc_h8_ = source32_.minCapacity
            d_194___mcc_h9_ = source32_.minOperands
            d_195___mcc_h10_ = source32_.pushes
            d_196___mcc_h11_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkgoldenrod")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "bisque")))
        elif source32_.is_BitwiseOp:
            d_197___mcc_h12_ = source32_.name
            d_198___mcc_h13_ = source32_.opcode
            d_199___mcc_h14_ = source32_.minCapacity
            d_200___mcc_h15_ = source32_.minOperands
            d_201___mcc_h16_ = source32_.pushes
            d_202___mcc_h17_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "orange")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#f3f383")))
        elif source32_.is_KeccakOp:
            d_203___mcc_h18_ = source32_.name
            d_204___mcc_h19_ = source32_.opcode
            d_205___mcc_h20_ = source32_.minCapacity
            d_206___mcc_h21_ = source32_.minOperands
            d_207___mcc_h22_ = source32_.pushes
            d_208___mcc_h23_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "grey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "linen")))
        elif source32_.is_EnvOp:
            d_209___mcc_h24_ = source32_.name
            d_210___mcc_h25_ = source32_.opcode
            d_211___mcc_h26_ = source32_.minCapacity
            d_212___mcc_h27_ = source32_.minOperands
            d_213___mcc_h28_ = source32_.pushes
            d_214___mcc_h29_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkslategrey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightgrey")))
        elif source32_.is_MemOp:
            d_215___mcc_h30_ = source32_.name
            d_216___mcc_h31_ = source32_.opcode
            d_217___mcc_h32_ = source32_.minCapacity
            d_218___mcc_h33_ = source32_.minOperands
            d_219___mcc_h34_ = source32_.pushes
            d_220___mcc_h35_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "wheat")))
        elif source32_.is_StorageOp:
            d_221___mcc_h36_ = source32_.name
            d_222___mcc_h37_ = source32_.opcode
            d_223___mcc_h38_ = source32_.minCapacity
            d_224___mcc_h39_ = source32_.minOperands
            d_225___mcc_h40_ = source32_.pushes
            d_226___mcc_h41_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "fuchsia")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "mistyrose")))
        elif source32_.is_JumpOp:
            d_227___mcc_h42_ = source32_.name
            d_228___mcc_h43_ = source32_.opcode
            d_229___mcc_h44_ = source32_.minCapacity
            d_230___mcc_h45_ = source32_.minOperands
            d_231___mcc_h46_ = source32_.pushes
            d_232___mcc_h47_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "purple")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "thistle")))
        elif source32_.is_RunOp:
            d_233___mcc_h48_ = source32_.name
            d_234___mcc_h49_ = source32_.opcode
            d_235___mcc_h50_ = source32_.minCapacity
            d_236___mcc_h51_ = source32_.minOperands
            d_237___mcc_h52_ = source32_.pushes
            d_238___mcc_h53_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tan")))
        elif source32_.is_StackOp:
            d_239___mcc_h54_ = source32_.name
            d_240___mcc_h55_ = source32_.opcode
            d_241___mcc_h56_ = source32_.minCapacity
            d_242___mcc_h57_ = source32_.minOperands
            d_243___mcc_h58_ = source32_.pushes
            d_244___mcc_h59_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "royalblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "powderblue")))
        elif source32_.is_LogOp:
            d_245___mcc_h60_ = source32_.name
            d_246___mcc_h61_ = source32_.opcode
            d_247___mcc_h62_ = source32_.minCapacity
            d_248___mcc_h63_ = source32_.minOperands
            d_249___mcc_h64_ = source32_.pushes
            d_250___mcc_h65_ = source32_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "cornflowerblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lavender")))
        elif True:
            d_251___mcc_h66_ = source32_.name
            d_252___mcc_h67_ = source32_.opcode
            d_253___mcc_h68_ = source32_.minCapacity
            d_254___mcc_h69_ = source32_.minOperands
            d_255___mcc_h70_ = source32_.pushes
            d_256___mcc_h71_ = source32_.pops
            d_257_opcode_ = d_252___mcc_h67_
            if ((d_257_opcode_) == (EVMConstants.default__.STOP)) or ((d_257_opcode_) == (EVMConstants.default__.REVERT)):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "brown")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightsalmon")))
            elif (d_257_opcode_) == (EVMConstants.default__.RETURN):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "teal")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "greenyellow")))
            elif ((((d_257_opcode_) == (EVMConstants.default__.CALL)) or ((d_257_opcode_) == (EVMConstants.default__.CALLCODE))) or ((d_257_opcode_) == (EVMConstants.default__.DELEGATECALL))) or ((d_257_opcode_) == (EVMConstants.default__.STATICCALL)):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tan")))
            elif True:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "brown")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "salmon")))


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
            d_258_k_: int = forall_var_2_
            return not (((0) <= (d_258_k_)) and ((d_258_k_) < (len((self).arg)))) or (Hex.default__.IsHex(((self).arg)[d_258_k_]))

        return ((((self).op).opcode) == (EVMConstants.default__.INVALID)) or ((not (((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32))) or (((len((self).arg)) == ((2) * ((((self).op).opcode) - (EVMConstants.default__.PUSH0)))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).arg)), True, lambda2_)))) and (not (not(((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32)))) or ((len((self).arg)) == (0))))

    def ToString(self):
        d_259_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_259_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_259_x_) if (len(d_259_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def ToHTMLTable(self, entryPortTag, exitPortTag):
        d_260_cols_ = default__.Colours(self)
        d_261_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_262___v0_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_263_gasLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981;"))
        d_264_oplineTD_ = ((((((((((((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" "))) + (entryPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x")))) + (d_261_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " </TD>\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: ")))) + (EVMToolTips.default__.Gas(((self).op).opcode))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " \" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "target=\"_blank\" href=\"")))) + (EVMToolTips.default__.gasRefLine)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (d_263_gasLine_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")))) + ((d_260_cols_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" align=\"left\" cellpadding=\"3\" ")))) + (exitPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"")))) + (EVMToolTips.default__.bytecodeRefLine)) + (Int.default__.NatToString((EVMToolTips.default__.ToolTip(((self).op).opcode))[1]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" target=\"_blank\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " tooltip=\"")))) + ((EVMToolTips.default__.ToolTip(((self).op).opcode))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\"")))) + ((d_260_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))
        d_265_arglineTD_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" align=\"left\">"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  0x")))) + ((self).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>"))) if (len((self).arg)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_266_lineTR_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR>"))) + (d_264_oplineTD_)) + (d_265_arglineTD_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR>")))
        d_267_itemTable_ = ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE  border=\"0\" cellpadding=\"0\" cellsborder=\"0\" CELLSPACING=\"1\">"))) + (d_266_lineTR_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>")))
        return d_267_itemTable_

    def IsTerminal(self):
        return ((self).op).IsTerminal()

    def IsJumpDest(self):
        return ((self).op).IsJumpDest()

    def IsJump(self):
        return ((self).op).IsJump()

    def StackEffect(self):
        return ((self).op).StackEffect()

    def WeakestPreOperands(self, post):
        return ((self).op).WeakestPreOperands(post)

    def WeakestPreCapacity(self, post):
        return ((self).op).WeakestPreCapacity(post)

    def StackPosBackWardTracker(self, pos_k):
        source33_ = (self).op
        if source33_.is_ArithOp:
            d_268___mcc_h0_ = source33_.name
            d_269___mcc_h1_ = source33_.opcode
            d_270___mcc_h2_ = source33_.minCapacity
            d_271___mcc_h3_ = source33_.minOperands
            d_272___mcc_h4_ = source33_.pushes
            d_273___mcc_h5_ = source33_.pops
            d_274_pops_ = d_273___mcc_h5_
            d_275_pushes_ = d_272___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source33_.is_CompOp:
            d_276___mcc_h6_ = source33_.name
            d_277___mcc_h7_ = source33_.opcode
            d_278___mcc_h8_ = source33_.minCapacity
            d_279___mcc_h9_ = source33_.minOperands
            d_280___mcc_h10_ = source33_.pushes
            d_281___mcc_h11_ = source33_.pops
            d_282_pops_ = d_281___mcc_h11_
            d_283_pushes_ = d_280___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_282_pops_)) - (d_283_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source33_.is_BitwiseOp:
            d_284___mcc_h12_ = source33_.name
            d_285___mcc_h13_ = source33_.opcode
            d_286___mcc_h14_ = source33_.minCapacity
            d_287___mcc_h15_ = source33_.minOperands
            d_288___mcc_h16_ = source33_.pushes
            d_289___mcc_h17_ = source33_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source33_.is_KeccakOp:
            d_290___mcc_h18_ = source33_.name
            d_291___mcc_h19_ = source33_.opcode
            d_292___mcc_h20_ = source33_.minCapacity
            d_293___mcc_h21_ = source33_.minOperands
            d_294___mcc_h22_ = source33_.pushes
            d_295___mcc_h23_ = source33_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source33_.is_EnvOp:
            d_296___mcc_h24_ = source33_.name
            d_297___mcc_h25_ = source33_.opcode
            d_298___mcc_h26_ = source33_.minCapacity
            d_299___mcc_h27_ = source33_.minOperands
            d_300___mcc_h28_ = source33_.pushes
            d_301___mcc_h29_ = source33_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source33_.is_MemOp:
            d_302___mcc_h30_ = source33_.name
            d_303___mcc_h31_ = source33_.opcode
            d_304___mcc_h32_ = source33_.minCapacity
            d_305___mcc_h33_ = source33_.minOperands
            d_306___mcc_h34_ = source33_.pushes
            d_307___mcc_h35_ = source33_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source33_.is_StorageOp:
            d_308___mcc_h36_ = source33_.name
            d_309___mcc_h37_ = source33_.opcode
            d_310___mcc_h38_ = source33_.minCapacity
            d_311___mcc_h39_ = source33_.minOperands
            d_312___mcc_h40_ = source33_.pushes
            d_313___mcc_h41_ = source33_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source33_.is_JumpOp:
            d_314___mcc_h42_ = source33_.name
            d_315___mcc_h43_ = source33_.opcode
            d_316___mcc_h44_ = source33_.minCapacity
            d_317___mcc_h45_ = source33_.minOperands
            d_318___mcc_h46_ = source33_.pushes
            d_319___mcc_h47_ = source33_.pops
            d_320_opcode_ = d_315___mcc_h43_
            if (d_320_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_320_opcode_)) and ((d_320_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_321_k_ = ((d_320_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_321_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source33_.is_RunOp:
            d_322___mcc_h48_ = source33_.name
            d_323___mcc_h49_ = source33_.opcode
            d_324___mcc_h50_ = source33_.minCapacity
            d_325___mcc_h51_ = source33_.minOperands
            d_326___mcc_h52_ = source33_.pushes
            d_327___mcc_h53_ = source33_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source33_.is_StackOp:
            d_328___mcc_h54_ = source33_.name
            d_329___mcc_h55_ = source33_.opcode
            d_330___mcc_h56_ = source33_.minCapacity
            d_331___mcc_h57_ = source33_.minOperands
            d_332___mcc_h58_ = source33_.pushes
            d_333___mcc_h59_ = source33_.pops
            d_334_opcode_ = d_329___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_334_opcode_)) and ((d_334_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_334_opcode_)) and ((d_334_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_334_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_334_opcode_)) and ((d_334_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_335_k_ = ((d_334_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_335_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_335_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source33_.is_LogOp:
            d_336___mcc_h60_ = source33_.name
            d_337___mcc_h61_ = source33_.opcode
            d_338___mcc_h62_ = source33_.minCapacity
            d_339___mcc_h63_ = source33_.minOperands
            d_340___mcc_h64_ = source33_.pushes
            d_341___mcc_h65_ = source33_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif True:
            d_342___mcc_h66_ = source33_.name
            d_343___mcc_h67_ = source33_.opcode
            d_344___mcc_h68_ = source33_.minCapacity
            d_345___mcc_h69_ = source33_.minOperands
            d_346___mcc_h70_ = source33_.pushes
            d_347___mcc_h71_ = source33_.pops
            return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))

    def NextState(self, s, cond):
        source34_ = (self).op
        if source34_.is_ArithOp:
            d_348___mcc_h0_ = source34_.name
            d_349___mcc_h1_ = source34_.opcode
            d_350___mcc_h2_ = source34_.minCapacity
            d_351___mcc_h3_ = source34_.minOperands
            d_352___mcc_h4_ = source34_.pushes
            d_353___mcc_h5_ = source34_.pops
            d_354_pops_ = d_353___mcc_h5_
            d_355_pushes_ = d_352___mcc_h4_
            if (((s).Size()) >= (d_354_pops_)) and (not(cond)):
                return (((s).PopN(d_354_pops_)).PushNRandom(d_355_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source34_.is_CompOp:
            d_356___mcc_h6_ = source34_.name
            d_357___mcc_h7_ = source34_.opcode
            d_358___mcc_h8_ = source34_.minCapacity
            d_359___mcc_h9_ = source34_.minOperands
            d_360___mcc_h10_ = source34_.pushes
            d_361___mcc_h11_ = source34_.pops
            d_362_pops_ = d_361___mcc_h11_
            d_363_pushes_ = d_360___mcc_h10_
            if (((s).Size()) >= (d_362_pops_)) and (not(cond)):
                return (((s).PopN(d_362_pops_)).PushNRandom(d_363_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source34_.is_BitwiseOp:
            d_364___mcc_h12_ = source34_.name
            d_365___mcc_h13_ = source34_.opcode
            d_366___mcc_h14_ = source34_.minCapacity
            d_367___mcc_h15_ = source34_.minOperands
            d_368___mcc_h16_ = source34_.pushes
            d_369___mcc_h17_ = source34_.pops
            d_370_pops_ = d_369___mcc_h17_
            d_371_pushes_ = d_368___mcc_h16_
            if (((s).Size()) >= (d_370_pops_)) and (not(cond)):
                return (((s).PopN(d_370_pops_)).PushNRandom(d_371_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source34_.is_KeccakOp:
            d_372___mcc_h18_ = source34_.name
            d_373___mcc_h19_ = source34_.opcode
            d_374___mcc_h20_ = source34_.minCapacity
            d_375___mcc_h21_ = source34_.minOperands
            d_376___mcc_h22_ = source34_.pushes
            d_377___mcc_h23_ = source34_.pops
            d_378_pops_ = d_377___mcc_h23_
            d_379_pushes_ = d_376___mcc_h22_
            if (((s).Size()) >= (2)) and (not(cond)):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source34_.is_EnvOp:
            d_380___mcc_h24_ = source34_.name
            d_381___mcc_h25_ = source34_.opcode
            d_382___mcc_h26_ = source34_.minCapacity
            d_383___mcc_h27_ = source34_.minOperands
            d_384___mcc_h28_ = source34_.pushes
            d_385___mcc_h29_ = source34_.pops
            d_386_pops_ = d_385___mcc_h29_
            d_387_pushes_ = d_384___mcc_h28_
            if (((s).Size()) >= (d_386_pops_)) and (not(cond)):
                return (((s).PopN(d_386_pops_)).PushNRandom(d_387_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        elif source34_.is_MemOp:
            d_388___mcc_h30_ = source34_.name
            d_389___mcc_h31_ = source34_.opcode
            d_390___mcc_h32_ = source34_.minCapacity
            d_391___mcc_h33_ = source34_.minOperands
            d_392___mcc_h34_ = source34_.pushes
            d_393___mcc_h35_ = source34_.pops
            d_394_pops_ = d_393___mcc_h35_
            d_395_pushes_ = d_392___mcc_h34_
            if (((s).Size()) >= (d_394_pops_)) and (not(cond)):
                return (((s).PopN(d_394_pops_)).PushNRandom(d_395_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        elif source34_.is_StorageOp:
            d_396___mcc_h36_ = source34_.name
            d_397___mcc_h37_ = source34_.opcode
            d_398___mcc_h38_ = source34_.minCapacity
            d_399___mcc_h39_ = source34_.minOperands
            d_400___mcc_h40_ = source34_.pushes
            d_401___mcc_h41_ = source34_.pops
            d_402_pops_ = d_401___mcc_h41_
            d_403_pushes_ = d_400___mcc_h40_
            if (((s).Size()) >= (d_402_pops_)) and (not(cond)):
                return (((s).PopN(d_402_pops_)).PushNRandom(d_403_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        elif source34_.is_JumpOp:
            d_404___mcc_h42_ = source34_.name
            d_405___mcc_h43_ = source34_.opcode
            d_406___mcc_h44_ = source34_.minCapacity
            d_407___mcc_h45_ = source34_.minOperands
            d_408___mcc_h46_ = source34_.pushes
            d_409___mcc_h47_ = source34_.pops
            d_410_pops_ = d_409___mcc_h47_
            d_411_pushes_ = d_408___mcc_h46_
            d_412_opcode_ = d_405___mcc_h43_
            if (d_412_opcode_) == (EVMConstants.default__.JUMPDEST):
                if not(cond):
                    return (s).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPDEST/exit true")))
            elif (d_412_opcode_) == (EVMConstants.default__.JUMP):
                if (((s).Size()) >= (1)) and (cond):
                    source35_ = (s).Peek(0)
                    if source35_.is_Value:
                        d_413___mcc_h72_ = source35_.v
                        d_414_v_ = d_413___mcc_h72_
                        return ((s).Pop()).Goto(d_414_v_)
                    elif True:
                        d_415___mcc_h73_ = source35_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_412_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source36_ = (s).Peek(0)
                    if source36_.is_Value:
                        d_416___mcc_h74_ = source36_.v
                        d_417_v_ = d_416___mcc_h74_
                        if cond:
                            return ((s).PopN(2)).Goto(d_417_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_418___mcc_h75_ = source36_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source34_.is_RunOp:
            d_419___mcc_h48_ = source34_.name
            d_420___mcc_h49_ = source34_.opcode
            d_421___mcc_h50_ = source34_.minCapacity
            d_422___mcc_h51_ = source34_.minOperands
            d_423___mcc_h52_ = source34_.pushes
            d_424___mcc_h53_ = source34_.pops
            d_425_pops_ = d_424___mcc_h53_
            d_426_pushes_ = d_423___mcc_h52_
            if not(cond):
                return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RunOp error")))
        elif source34_.is_StackOp:
            d_427___mcc_h54_ = source34_.name
            d_428___mcc_h55_ = source34_.opcode
            d_429___mcc_h56_ = source34_.minCapacity
            d_430___mcc_h57_ = source34_.minOperands
            d_431___mcc_h58_ = source34_.pushes
            d_432___mcc_h59_ = source34_.pops
            d_433_pops_ = d_432___mcc_h59_
            d_434_pushes_ = d_431___mcc_h58_
            d_435_opcode_ = d_428___mcc_h55_
            if (((d_435_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1))) and (not(cond)):
                return ((s).Pop()).Skip(1)
            elif (((EVMConstants.default__.PUSH0) <= (d_435_opcode_)) and ((d_435_opcode_) <= (EVMConstants.default__.PUSH32))) and (not(cond)):
                return ((s).Push(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))).Skip((1) + ((d_435_opcode_) - (EVMConstants.default__.PUSH0)))
            elif ((((EVMConstants.default__.DUP1) <= (d_435_opcode_)) and ((d_435_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_435_opcode_) - (EVMConstants.default__.DUP1)) + (1)))) and (not(cond)):
                return ((s).Dup(((d_435_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif ((((EVMConstants.default__.SWAP1) <= (d_435_opcode_)) and ((d_435_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_435_opcode_) - (EVMConstants.default__.SWAP1)) + (1)))) and (not(cond)):
                return ((s).Swap(((d_435_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        elif source34_.is_LogOp:
            d_436___mcc_h60_ = source34_.name
            d_437___mcc_h61_ = source34_.opcode
            d_438___mcc_h62_ = source34_.minCapacity
            d_439___mcc_h63_ = source34_.minOperands
            d_440___mcc_h64_ = source34_.pushes
            d_441___mcc_h65_ = source34_.pops
            d_442_pops_ = d_441___mcc_h65_
            d_443_pushes_ = d_440___mcc_h64_
            if (((s).Size()) >= (d_442_pops_)) and (not(cond)):
                return ((s).PopN(d_442_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        elif True:
            d_444___mcc_h66_ = source34_.name
            d_445___mcc_h67_ = source34_.opcode
            d_446___mcc_h68_ = source34_.minCapacity
            d_447___mcc_h69_ = source34_.minOperands
            d_448___mcc_h70_ = source34_.pushes
            d_449___mcc_h71_ = source34_.pops
            d_450_pops_ = d_449___mcc_h71_
            d_451_pushes_ = d_448___mcc_h70_
            if (((s).Size()) >= (d_450_pops_)) and (not(cond)):
                return (((s).PopN(d_450_pops_)).PushNRandom(d_451_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source37_ = (self).op
        if source37_.is_ArithOp:
            d_452___mcc_h0_ = source37_.name
            d_453___mcc_h1_ = source37_.opcode
            d_454___mcc_h2_ = source37_.minCapacity
            d_455___mcc_h3_ = source37_.minOperands
            d_456___mcc_h4_ = source37_.pushes
            d_457___mcc_h5_ = source37_.pops
            d_458_pops_ = d_457___mcc_h5_
            d_459_pushes_ = d_456___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda3_(d_461_pos_):
                    return (d_461_pos_) + (1)

                d_460_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda3_)
                return WeakPre.Cond_StCond(d_460_shiftByOne_, (c).TrackedVals())
        elif source37_.is_CompOp:
            d_462___mcc_h6_ = source37_.name
            d_463___mcc_h7_ = source37_.opcode
            d_464___mcc_h8_ = source37_.minCapacity
            d_465___mcc_h9_ = source37_.minOperands
            d_466___mcc_h10_ = source37_.pushes
            d_467___mcc_h11_ = source37_.pops
            d_468_pops_ = d_467___mcc_h11_
            d_469_pushes_ = d_466___mcc_h10_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda4_(d_471_pops_, d_472_pushes_):
                    def lambda5_(d_473_pos_):
                        return ((d_473_pos_) + (d_471_pops_)) - (d_472_pushes_)

                    return lambda5_

                d_470_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda4_(d_468_pops_, d_469_pushes_))
                return WeakPre.Cond_StCond(d_470_shiftBy_, (c).TrackedVals())
        elif source37_.is_BitwiseOp:
            d_474___mcc_h12_ = source37_.name
            d_475___mcc_h13_ = source37_.opcode
            d_476___mcc_h14_ = source37_.minCapacity
            d_477___mcc_h15_ = source37_.minOperands
            d_478___mcc_h16_ = source37_.pushes
            d_479___mcc_h17_ = source37_.pops
            d_480_pops_ = d_479___mcc_h17_
            d_481_pushes_ = d_478___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda6_(d_483_pops_, d_484_pushes_):
                    def lambda7_(d_485_pos_):
                        return ((d_485_pos_) + (d_483_pops_)) - (d_484_pushes_)

                    return lambda7_

                d_482_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_(d_480_pops_, d_481_pushes_))
                return WeakPre.Cond_StCond(d_482_shiftBy_, (c).TrackedVals())
        elif source37_.is_KeccakOp:
            d_486___mcc_h18_ = source37_.name
            d_487___mcc_h19_ = source37_.opcode
            d_488___mcc_h20_ = source37_.minCapacity
            d_489___mcc_h21_ = source37_.minOperands
            d_490___mcc_h22_ = source37_.pushes
            d_491___mcc_h23_ = source37_.pops
            d_492_pops_ = d_491___mcc_h23_
            d_493_pushes_ = d_490___mcc_h22_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda8_(d_495_pos_):
                    return (d_495_pos_) + (1)

                d_494_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda8_)
                return WeakPre.Cond_StCond(d_494_shiftByOne_, (c).TrackedVals())
        elif source37_.is_EnvOp:
            d_496___mcc_h24_ = source37_.name
            d_497___mcc_h25_ = source37_.opcode
            d_498___mcc_h26_ = source37_.minCapacity
            d_499___mcc_h27_ = source37_.minOperands
            d_500___mcc_h28_ = source37_.pushes
            d_501___mcc_h29_ = source37_.pops
            d_502_pops_ = d_501___mcc_h29_
            d_503_pushes_ = d_500___mcc_h28_
            if ((d_503_pushes_) == (1)) and ((d_502_pops_) == (0)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda9_(d_505_pos_):
                        return (d_505_pos_) - (1)

                    d_504_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda9_)
                    return WeakPre.Cond_StCond(d_504_shiftByOne_, (c).TrackedVals())
            elif ((d_503_pushes_) == (1)) and ((d_502_pops_) == (1)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
            elif True:
                def lambda10_(d_507_pops_, d_508_pushes_):
                    def lambda11_(d_509_pos_):
                        return ((d_509_pos_) + (d_507_pops_)) - (d_508_pushes_)

                    return lambda11_

                d_506_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda10_(d_502_pops_, d_503_pushes_))
                return WeakPre.Cond_StCond(d_506_shiftBy_, (c).TrackedVals())
        elif source37_.is_MemOp:
            d_510___mcc_h30_ = source37_.name
            d_511___mcc_h31_ = source37_.opcode
            d_512___mcc_h32_ = source37_.minCapacity
            d_513___mcc_h33_ = source37_.minOperands
            d_514___mcc_h34_ = source37_.pushes
            d_515___mcc_h35_ = source37_.pops
            d_516_pops_ = d_515___mcc_h35_
            d_517_pushes_ = d_514___mcc_h34_
            if (d_517_pushes_) == (0):
                def lambda12_(d_519_pos_):
                    return (d_519_pos_) + (2)

                d_518_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda12_)
                return WeakPre.Cond_StCond(d_518_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source37_.is_StorageOp:
            d_520___mcc_h36_ = source37_.name
            d_521___mcc_h37_ = source37_.opcode
            d_522___mcc_h38_ = source37_.minCapacity
            d_523___mcc_h39_ = source37_.minOperands
            d_524___mcc_h40_ = source37_.pushes
            d_525___mcc_h41_ = source37_.pops
            d_526_pops_ = d_525___mcc_h41_
            d_527_pushes_ = d_524___mcc_h40_
            if (d_527_pushes_) == (0):
                def lambda13_(d_529_pos_):
                    return (d_529_pos_) + (2)

                d_528_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda13_)
                return WeakPre.Cond_StCond(d_528_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source37_.is_JumpOp:
            d_530___mcc_h42_ = source37_.name
            d_531___mcc_h43_ = source37_.opcode
            d_532___mcc_h44_ = source37_.minCapacity
            d_533___mcc_h45_ = source37_.minOperands
            d_534___mcc_h46_ = source37_.pushes
            d_535___mcc_h47_ = source37_.pops
            d_536_opcode_ = d_531___mcc_h43_
            if (d_536_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_536_opcode_)) and ((d_536_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_537_k_ = ((d_536_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda14_(d_539_k_):
                    def lambda15_(d_540_pos_):
                        return (d_540_pos_) + (d_539_k_)

                    return lambda15_

                d_538_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda14_(d_537_k_))
                return WeakPre.Cond_StCond(d_538_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source37_.is_RunOp:
            d_541___mcc_h48_ = source37_.name
            d_542___mcc_h49_ = source37_.opcode
            d_543___mcc_h50_ = source37_.minCapacity
            d_544___mcc_h51_ = source37_.minOperands
            d_545___mcc_h52_ = source37_.pushes
            d_546___mcc_h53_ = source37_.pops
            d_547_opcode_ = d_542___mcc_h49_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda16_(d_549_pos_):
                    return (d_549_pos_) - (1)

                d_548_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                return WeakPre.Cond_StCond(d_548_shiftByOne_, (c).TrackedVals())
        elif source37_.is_StackOp:
            d_550___mcc_h54_ = source37_.name
            d_551___mcc_h55_ = source37_.opcode
            d_552___mcc_h56_ = source37_.minCapacity
            d_553___mcc_h57_ = source37_.minOperands
            d_554___mcc_h58_ = source37_.pushes
            d_555___mcc_h59_ = source37_.pops
            d_556_opcode_ = d_551___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_556_opcode_)) and ((d_556_opcode_) <= (EVMConstants.default__.PUSH32)):
                source38_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source38_.is_None:
                    def lambda17_(d_558_pos_):
                        return (d_558_pos_) - (1)

                    d_557_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda17_)
                    return WeakPre.Cond_StCond(d_557_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_559___mcc_h72_ = source38_.v
                    d_560_i_ = d_559___mcc_h72_
                    d_561_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_562___v158_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_560_i_)) == ((d_561_argVal_).Extract()):
                        d_563_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_560_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_560_i_) + (1)::]))
                        if (len(d_563_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda18_(d_565_pos_):
                                return (d_565_pos_) - (1)

                            d_564_shiftByMinusOne_ = MiscTypes.default__.Map(d_563_filtered_, lambda18_)
                            return WeakPre.Cond_StCond(d_564_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_560_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_560_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_556_opcode_)) and ((d_556_opcode_) <= (EVMConstants.default__.DUP16)):
                source39_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source39_.is_None:
                    def lambda19_(d_567_pos_):
                        return (d_567_pos_) - (1)

                    d_566_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda19_)
                    return WeakPre.Cond_StCond(d_566_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_568___mcc_h73_ = source39_.v
                    d_569_index0_ = d_568___mcc_h73_
                    source40_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_556_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source40_.is_None:
                        def lambda20_(d_571_opcode_):
                            def lambda21_(d_572_pos_):
                                return ((d_571_opcode_) - (EVMConstants.default__.DUP1) if (d_572_pos_) == (0) else (d_572_pos_) - (1))

                            return lambda21_

                        d_570_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda20_(d_556_opcode_))
                        return WeakPre.Cond_StCond(d_570_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_573___mcc_h74_ = source40_.v
                        d_574_index_ = d_573___mcc_h74_
                        if ((c).TrackedValAt(d_569_index0_)) == ((c).TrackedValAt(d_574_index_)):
                            d_575_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_569_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_569_index0_) + (1)::]))
                            def lambda22_(d_577_pos_):
                                return (d_577_pos_) - (1)

                            d_576_shiftByMinusOne_ = MiscTypes.default__.Map(d_575_filtered_, lambda22_)
                            return WeakPre.Cond_StCond(d_576_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_569_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_569_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_556_opcode_)) and ((d_556_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_578_k_ = ((d_556_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda23_(d_580_k_):
                    def lambda24_(d_581_pos_):
                        return (d_580_k_ if (d_581_pos_) == (0) else (0 if (d_581_pos_) == (d_580_k_) else d_581_pos_))

                    return lambda24_

                d_579_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda23_(d_578_k_))
                return WeakPre.Cond_StCond(d_579_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda25_(d_583_i_):
                    return (d_583_i_) + (1)

                d_582_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda25_)
                return WeakPre.Cond_StCond(d_582_shiftByOne_, (c).TrackedVals())
        elif source37_.is_LogOp:
            d_584___mcc_h60_ = source37_.name
            d_585___mcc_h61_ = source37_.opcode
            d_586___mcc_h62_ = source37_.minCapacity
            d_587___mcc_h63_ = source37_.minOperands
            d_588___mcc_h64_ = source37_.pushes
            d_589___mcc_h65_ = source37_.pops
            d_590_pops_ = d_589___mcc_h65_
            d_591_pushes_ = d_588___mcc_h64_
            d_592_opcode_ = d_585___mcc_h61_
            def lambda26_(d_594_pops_):
                def lambda27_(d_595_pos_):
                    return (d_595_pos_) + (d_594_pops_)

                return lambda27_

            d_593_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda26_(d_590_pops_))
            return WeakPre.Cond_StCond(d_593_shiftBy_, (c).TrackedVals())
        elif True:
            d_596___mcc_h66_ = source37_.name
            d_597___mcc_h67_ = source37_.opcode
            d_598___mcc_h68_ = source37_.minCapacity
            d_599___mcc_h69_ = source37_.minOperands
            d_600___mcc_h70_ = source37_.pushes
            d_601___mcc_h71_ = source37_.pops
            d_602_pops_ = d_601___mcc_h71_
            d_603_pushes_ = d_600___mcc_h70_
            d_604_opcode_ = d_597___mcc_h67_
            if (d_603_pushes_) == (0):
                def lambda28_(d_606_pops_):
                    def lambda29_(d_607_pos_):
                        return (d_607_pos_) + (d_606_pops_)

                    return lambda29_

                d_605_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda28_(d_602_pops_))
                return WeakPre.Cond_StCond(d_605_shiftBy_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda30_(d_609_pops_):
                        def lambda31_(d_610_pos_):
                            return (d_610_pos_) + (d_609_pops_)

                        return lambda31_

                    d_608_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda30_(d_602_pops_))
                    return WeakPre.Cond_StCond(d_608_shiftBy_, (c).TrackedVals())


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

