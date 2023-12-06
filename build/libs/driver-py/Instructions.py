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
        d_183_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_184___v149_ in range((64) - (len(xc)))])
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

    def ToHTML(self):
        d_260_x_ = (self).arg
        d_261_cols_ = default__.Colours(self)
        d_262_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_263___v0_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_264_insText_ = (((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_261_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_260_x_) if (((self).op).opcode) == (EVMConstants.default__.INVALID) else (((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_261_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_260_x_) if (len(d_260_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))))
        return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (d_262_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":")))) + (d_264_insText_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))

    def ToHTMLTable(self, entryPortTag, exitPortTag):
        d_265_cols_ = default__.Colours(self)
        d_266_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_267___v1_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_268_gasLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981;"))
        d_269_oplineTD_ = ((((((((((((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" "))) + (entryPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x")))) + (d_266_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " </TD>\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: ")))) + (EVMToolTips.default__.Gas(((self).op).opcode))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " \" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "target=\"_blank\" href=\"")))) + (EVMToolTips.default__.gasRefLine)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (d_268_gasLine_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")))) + ((d_265_cols_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" align=\"left\" cellpadding=\"3\" ")))) + (exitPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"")))) + (EVMToolTips.default__.bytecodeRefLine)) + (Int.default__.NatToString((EVMToolTips.default__.ToolTip(((self).op).opcode))[1]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" target=\"_blank\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " tooltip=\"")))) + ((EVMToolTips.default__.ToolTip(((self).op).opcode))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\"")))) + ((d_265_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))
        d_270_arglineTD_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" align=\"left\">"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  0x")))) + ((self).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>"))) if (len((self).arg)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_271_lineTR_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR>"))) + (d_269_oplineTD_)) + (d_270_arglineTD_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR>")))
        d_272_itemTable_ = ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE  border=\"0\" cellpadding=\"0\" cellsborder=\"0\" CELLSPACING=\"1\">"))) + (d_271_lineTR_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>")))
        return d_272_itemTable_

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
            d_273___mcc_h0_ = source33_.name
            d_274___mcc_h1_ = source33_.opcode
            d_275___mcc_h2_ = source33_.minCapacity
            d_276___mcc_h3_ = source33_.minOperands
            d_277___mcc_h4_ = source33_.pushes
            d_278___mcc_h5_ = source33_.pops
            d_279_pops_ = d_278___mcc_h5_
            d_280_pushes_ = d_277___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source33_.is_CompOp:
            d_281___mcc_h6_ = source33_.name
            d_282___mcc_h7_ = source33_.opcode
            d_283___mcc_h8_ = source33_.minCapacity
            d_284___mcc_h9_ = source33_.minOperands
            d_285___mcc_h10_ = source33_.pushes
            d_286___mcc_h11_ = source33_.pops
            d_287_pops_ = d_286___mcc_h11_
            d_288_pushes_ = d_285___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_287_pops_)) - (d_288_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source33_.is_BitwiseOp:
            d_289___mcc_h12_ = source33_.name
            d_290___mcc_h13_ = source33_.opcode
            d_291___mcc_h14_ = source33_.minCapacity
            d_292___mcc_h15_ = source33_.minOperands
            d_293___mcc_h16_ = source33_.pushes
            d_294___mcc_h17_ = source33_.pops
            d_295_pops_ = d_294___mcc_h17_
            d_296_pushes_ = d_293___mcc_h16_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_295_pops_)) - (d_296_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Bitwise operator with target 0"))))
        elif source33_.is_KeccakOp:
            d_297___mcc_h18_ = source33_.name
            d_298___mcc_h19_ = source33_.opcode
            d_299___mcc_h20_ = source33_.minCapacity
            d_300___mcc_h21_ = source33_.minOperands
            d_301___mcc_h22_ = source33_.pushes
            d_302___mcc_h23_ = source33_.pops
            d_303_pops_ = d_302___mcc_h23_
            d_304_pushes_ = d_301___mcc_h22_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Keccak operator with target 0"))))
        elif source33_.is_EnvOp:
            d_305___mcc_h24_ = source33_.name
            d_306___mcc_h25_ = source33_.opcode
            d_307___mcc_h26_ = source33_.minCapacity
            d_308___mcc_h27_ = source33_.minOperands
            d_309___mcc_h28_ = source33_.pushes
            d_310___mcc_h29_ = source33_.pops
            d_311_pops_ = d_310___mcc_h29_
            d_312_pushes_ = d_309___mcc_h28_
            if ((d_312_pushes_) == (1)) and ((d_311_pops_) == (0)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((d_312_pushes_) == (1)) and ((d_311_pops_) == (1)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
            elif True:
                return MiscTypes.Either_Right(((pos_k) + (d_311_pops_)) - (d_312_pushes_))
        elif source33_.is_MemOp:
            d_313___mcc_h30_ = source33_.name
            d_314___mcc_h31_ = source33_.opcode
            d_315___mcc_h32_ = source33_.minCapacity
            d_316___mcc_h33_ = source33_.minOperands
            d_317___mcc_h34_ = source33_.pushes
            d_318___mcc_h35_ = source33_.pops
            d_319_pops_ = d_318___mcc_h35_
            d_320_pushes_ = d_317___mcc_h34_
            if (d_320_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Mem operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source33_.is_StorageOp:
            d_321___mcc_h36_ = source33_.name
            d_322___mcc_h37_ = source33_.opcode
            d_323___mcc_h38_ = source33_.minCapacity
            d_324___mcc_h39_ = source33_.minOperands
            d_325___mcc_h40_ = source33_.pushes
            d_326___mcc_h41_ = source33_.pops
            d_327_pops_ = d_326___mcc_h41_
            d_328_pushes_ = d_325___mcc_h40_
            if (d_328_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Storage operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source33_.is_JumpOp:
            d_329___mcc_h42_ = source33_.name
            d_330___mcc_h43_ = source33_.opcode
            d_331___mcc_h44_ = source33_.minCapacity
            d_332___mcc_h45_ = source33_.minOperands
            d_333___mcc_h46_ = source33_.pushes
            d_334___mcc_h47_ = source33_.pops
            d_335_opcode_ = d_330___mcc_h43_
            if (d_335_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_335_opcode_)) and ((d_335_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_336_k_ = ((d_335_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_336_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source33_.is_RunOp:
            d_337___mcc_h48_ = source33_.name
            d_338___mcc_h49_ = source33_.opcode
            d_339___mcc_h50_ = source33_.minCapacity
            d_340___mcc_h51_ = source33_.minOperands
            d_341___mcc_h52_ = source33_.pushes
            d_342___mcc_h53_ = source33_.pops
            d_343_pops_ = d_342___mcc_h53_
            d_344_pushes_ = d_341___mcc_h52_
            if (pos_k) == (0):
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Run operator with target 0"))))
            elif True:
                return MiscTypes.Either_Right((pos_k) - (1))
        elif source33_.is_StackOp:
            d_345___mcc_h54_ = source33_.name
            d_346___mcc_h55_ = source33_.opcode
            d_347___mcc_h56_ = source33_.minCapacity
            d_348___mcc_h57_ = source33_.minOperands
            d_349___mcc_h58_ = source33_.pushes
            d_350___mcc_h59_ = source33_.pops
            d_351_opcode_ = d_346___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_351_opcode_)) and ((d_351_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_351_opcode_)) and ((d_351_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_351_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_351_opcode_)) and ((d_351_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_352_k_ = ((d_351_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_352_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_352_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source33_.is_LogOp:
            d_353___mcc_h60_ = source33_.name
            d_354___mcc_h61_ = source33_.opcode
            d_355___mcc_h62_ = source33_.minCapacity
            d_356___mcc_h63_ = source33_.minOperands
            d_357___mcc_h64_ = source33_.pushes
            d_358___mcc_h65_ = source33_.pops
            d_359_pops_ = d_358___mcc_h65_
            d_360_pushes_ = d_357___mcc_h64_
            return MiscTypes.Either_Right((pos_k) + (2))
        elif True:
            d_361___mcc_h66_ = source33_.name
            d_362___mcc_h67_ = source33_.opcode
            d_363___mcc_h68_ = source33_.minCapacity
            d_364___mcc_h69_ = source33_.minOperands
            d_365___mcc_h70_ = source33_.pushes
            d_366___mcc_h71_ = source33_.pops
            d_367_pops_ = d_366___mcc_h71_
            d_368_pushes_ = d_365___mcc_h70_
            if (d_368_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (d_367_pops_))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Sys operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) + (d_367_pops_))

    def NextState(self, s, jumpDests, cond):
        source34_ = (self).op
        if source34_.is_ArithOp:
            d_369___mcc_h0_ = source34_.name
            d_370___mcc_h1_ = source34_.opcode
            d_371___mcc_h2_ = source34_.minCapacity
            d_372___mcc_h3_ = source34_.minOperands
            d_373___mcc_h4_ = source34_.pushes
            d_374___mcc_h5_ = source34_.pops
            d_375_pops_ = d_374___mcc_h5_
            d_376_pushes_ = d_373___mcc_h4_
            if (((s).Size()) >= (d_375_pops_)) and (not(cond)):
                return (((s).PopN(d_375_pops_)).PushNRandom(d_376_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source34_.is_CompOp:
            d_377___mcc_h6_ = source34_.name
            d_378___mcc_h7_ = source34_.opcode
            d_379___mcc_h8_ = source34_.minCapacity
            d_380___mcc_h9_ = source34_.minOperands
            d_381___mcc_h10_ = source34_.pushes
            d_382___mcc_h11_ = source34_.pops
            d_383_pops_ = d_382___mcc_h11_
            d_384_pushes_ = d_381___mcc_h10_
            if (((s).Size()) >= (d_383_pops_)) and (not(cond)):
                return (((s).PopN(d_383_pops_)).PushNRandom(d_384_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source34_.is_BitwiseOp:
            d_385___mcc_h12_ = source34_.name
            d_386___mcc_h13_ = source34_.opcode
            d_387___mcc_h14_ = source34_.minCapacity
            d_388___mcc_h15_ = source34_.minOperands
            d_389___mcc_h16_ = source34_.pushes
            d_390___mcc_h17_ = source34_.pops
            d_391_pops_ = d_390___mcc_h17_
            d_392_pushes_ = d_389___mcc_h16_
            if (((s).Size()) >= (d_391_pops_)) and (not(cond)):
                return (((s).PopN(d_391_pops_)).PushNRandom(d_392_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source34_.is_KeccakOp:
            d_393___mcc_h18_ = source34_.name
            d_394___mcc_h19_ = source34_.opcode
            d_395___mcc_h20_ = source34_.minCapacity
            d_396___mcc_h21_ = source34_.minOperands
            d_397___mcc_h22_ = source34_.pushes
            d_398___mcc_h23_ = source34_.pops
            d_399_pops_ = d_398___mcc_h23_
            d_400_pushes_ = d_397___mcc_h22_
            if (((s).Size()) >= (2)) and (not(cond)):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source34_.is_EnvOp:
            d_401___mcc_h24_ = source34_.name
            d_402___mcc_h25_ = source34_.opcode
            d_403___mcc_h26_ = source34_.minCapacity
            d_404___mcc_h27_ = source34_.minOperands
            d_405___mcc_h28_ = source34_.pushes
            d_406___mcc_h29_ = source34_.pops
            d_407_pops_ = d_406___mcc_h29_
            d_408_pushes_ = d_405___mcc_h28_
            if (((s).Size()) >= (d_407_pops_)) and (not(cond)):
                return (((s).PopN(d_407_pops_)).PushNRandom(d_408_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        elif source34_.is_MemOp:
            d_409___mcc_h30_ = source34_.name
            d_410___mcc_h31_ = source34_.opcode
            d_411___mcc_h32_ = source34_.minCapacity
            d_412___mcc_h33_ = source34_.minOperands
            d_413___mcc_h34_ = source34_.pushes
            d_414___mcc_h35_ = source34_.pops
            d_415_pops_ = d_414___mcc_h35_
            d_416_pushes_ = d_413___mcc_h34_
            if (((s).Size()) >= (d_415_pops_)) and (not(cond)):
                return (((s).PopN(d_415_pops_)).PushNRandom(d_416_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        elif source34_.is_StorageOp:
            d_417___mcc_h36_ = source34_.name
            d_418___mcc_h37_ = source34_.opcode
            d_419___mcc_h38_ = source34_.minCapacity
            d_420___mcc_h39_ = source34_.minOperands
            d_421___mcc_h40_ = source34_.pushes
            d_422___mcc_h41_ = source34_.pops
            d_423_pops_ = d_422___mcc_h41_
            d_424_pushes_ = d_421___mcc_h40_
            if (((s).Size()) >= (d_423_pops_)) and (not(cond)):
                return (((s).PopN(d_423_pops_)).PushNRandom(d_424_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        elif source34_.is_JumpOp:
            d_425___mcc_h42_ = source34_.name
            d_426___mcc_h43_ = source34_.opcode
            d_427___mcc_h44_ = source34_.minCapacity
            d_428___mcc_h45_ = source34_.minOperands
            d_429___mcc_h46_ = source34_.pushes
            d_430___mcc_h47_ = source34_.pops
            d_431_pops_ = d_430___mcc_h47_
            d_432_pushes_ = d_429___mcc_h46_
            d_433_opcode_ = d_426___mcc_h43_
            if (d_433_opcode_) == (EVMConstants.default__.JUMPDEST):
                if not(cond):
                    return (s).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPDEST/exit true")))
            elif (d_433_opcode_) == (EVMConstants.default__.JUMP):
                if (((s).Size()) >= (1)) and (cond):
                    source35_ = (s).Peek(0)
                    if source35_.is_Value:
                        d_434___mcc_h72_ = source35_.v
                        d_435_v_ = d_434___mcc_h72_
                        return ((s).Pop()).Goto(d_435_v_)
                    elif True:
                        d_436___mcc_h73_ = source35_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_433_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source36_ = (s).Peek(0)
                    if source36_.is_Value:
                        d_437___mcc_h74_ = source36_.v
                        d_438_v_ = d_437___mcc_h74_
                        if cond:
                            return ((s).PopN(2)).Goto(d_438_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_439___mcc_h75_ = source36_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source34_.is_RunOp:
            d_440___mcc_h48_ = source34_.name
            d_441___mcc_h49_ = source34_.opcode
            d_442___mcc_h50_ = source34_.minCapacity
            d_443___mcc_h51_ = source34_.minOperands
            d_444___mcc_h52_ = source34_.pushes
            d_445___mcc_h53_ = source34_.pops
            d_446_pops_ = d_445___mcc_h53_
            d_447_pushes_ = d_444___mcc_h52_
            if not(cond):
                return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RunOp error")))
        elif source34_.is_StackOp:
            d_448___mcc_h54_ = source34_.name
            d_449___mcc_h55_ = source34_.opcode
            d_450___mcc_h56_ = source34_.minCapacity
            d_451___mcc_h57_ = source34_.minOperands
            d_452___mcc_h58_ = source34_.pushes
            d_453___mcc_h59_ = source34_.pops
            d_454_pops_ = d_453___mcc_h59_
            d_455_pushes_ = d_452___mcc_h58_
            d_456_opcode_ = d_449___mcc_h55_
            if (((d_456_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1))) and (not(cond)):
                return ((s).Pop()).Skip(1)
            elif (((EVMConstants.default__.PUSH0) <= (d_456_opcode_)) and ((d_456_opcode_) <= (EVMConstants.default__.PUSH32))) and (not(cond)):
                d_457_valToPush_ = (StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)) if (default__.GetArgValuePush((self).arg)) in (jumpDests) else StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))
                return ((s).Push(d_457_valToPush_)).Skip((1) + ((d_456_opcode_) - (EVMConstants.default__.PUSH0)))
            elif ((((EVMConstants.default__.DUP1) <= (d_456_opcode_)) and ((d_456_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_456_opcode_) - (EVMConstants.default__.DUP1)) + (1)))) and (not(cond)):
                return ((s).Dup(((d_456_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif ((((EVMConstants.default__.SWAP1) <= (d_456_opcode_)) and ((d_456_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_456_opcode_) - (EVMConstants.default__.SWAP1)) + (1)))) and (not(cond)):
                return ((s).Swap(((d_456_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        elif source34_.is_LogOp:
            d_458___mcc_h60_ = source34_.name
            d_459___mcc_h61_ = source34_.opcode
            d_460___mcc_h62_ = source34_.minCapacity
            d_461___mcc_h63_ = source34_.minOperands
            d_462___mcc_h64_ = source34_.pushes
            d_463___mcc_h65_ = source34_.pops
            d_464_pops_ = d_463___mcc_h65_
            d_465_pushes_ = d_462___mcc_h64_
            if (((s).Size()) >= (d_464_pops_)) and (not(cond)):
                return ((s).PopN(d_464_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        elif True:
            d_466___mcc_h66_ = source34_.name
            d_467___mcc_h67_ = source34_.opcode
            d_468___mcc_h68_ = source34_.minCapacity
            d_469___mcc_h69_ = source34_.minOperands
            d_470___mcc_h70_ = source34_.pushes
            d_471___mcc_h71_ = source34_.pops
            d_472_pops_ = d_471___mcc_h71_
            d_473_pushes_ = d_470___mcc_h70_
            d_474_op_ = d_467___mcc_h67_
            if (((d_474_op_) == (EVMConstants.default__.INVALID)) or ((d_474_op_) == (EVMConstants.default__.STOP))) or ((d_474_op_) == (EVMConstants.default__.REVERT)):
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))
            elif (((s).Size()) >= (d_472_pops_)) and (not(cond)):
                return (((s).PopN(d_472_pops_)).PushNRandom(d_473_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source37_ = (self).op
        if source37_.is_ArithOp:
            d_475___mcc_h0_ = source37_.name
            d_476___mcc_h1_ = source37_.opcode
            d_477___mcc_h2_ = source37_.minCapacity
            d_478___mcc_h3_ = source37_.minOperands
            d_479___mcc_h4_ = source37_.pushes
            d_480___mcc_h5_ = source37_.pops
            d_481_pops_ = d_480___mcc_h5_
            d_482_pushes_ = d_479___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda3_(d_484_pos_):
                    return (d_484_pos_) + (1)

                d_483_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda3_)
                return WeakPre.Cond_StCond(d_483_shiftByOne_, (c).TrackedVals())
        elif source37_.is_CompOp:
            d_485___mcc_h6_ = source37_.name
            d_486___mcc_h7_ = source37_.opcode
            d_487___mcc_h8_ = source37_.minCapacity
            d_488___mcc_h9_ = source37_.minOperands
            d_489___mcc_h10_ = source37_.pushes
            d_490___mcc_h11_ = source37_.pops
            d_491_pops_ = d_490___mcc_h11_
            d_492_pushes_ = d_489___mcc_h10_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda4_(d_494_pops_, d_495_pushes_):
                    def lambda5_(d_496_pos_):
                        return ((d_496_pos_) + (d_494_pops_)) - (d_495_pushes_)

                    return lambda5_

                d_493_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda4_(d_491_pops_, d_492_pushes_))
                return WeakPre.Cond_StCond(d_493_shiftBy_, (c).TrackedVals())
        elif source37_.is_BitwiseOp:
            d_497___mcc_h12_ = source37_.name
            d_498___mcc_h13_ = source37_.opcode
            d_499___mcc_h14_ = source37_.minCapacity
            d_500___mcc_h15_ = source37_.minOperands
            d_501___mcc_h16_ = source37_.pushes
            d_502___mcc_h17_ = source37_.pops
            d_503_pops_ = d_502___mcc_h17_
            d_504_pushes_ = d_501___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda6_(d_506_pops_, d_507_pushes_):
                    def lambda7_(d_508_pos_):
                        return ((d_508_pos_) + (d_506_pops_)) - (d_507_pushes_)

                    return lambda7_

                d_505_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_(d_503_pops_, d_504_pushes_))
                return WeakPre.Cond_StCond(d_505_shiftBy_, (c).TrackedVals())
        elif source37_.is_KeccakOp:
            d_509___mcc_h18_ = source37_.name
            d_510___mcc_h19_ = source37_.opcode
            d_511___mcc_h20_ = source37_.minCapacity
            d_512___mcc_h21_ = source37_.minOperands
            d_513___mcc_h22_ = source37_.pushes
            d_514___mcc_h23_ = source37_.pops
            d_515_pops_ = d_514___mcc_h23_
            d_516_pushes_ = d_513___mcc_h22_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda8_(d_518_pos_):
                    return (d_518_pos_) + (1)

                d_517_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda8_)
                return WeakPre.Cond_StCond(d_517_shiftByOne_, (c).TrackedVals())
        elif source37_.is_EnvOp:
            d_519___mcc_h24_ = source37_.name
            d_520___mcc_h25_ = source37_.opcode
            d_521___mcc_h26_ = source37_.minCapacity
            d_522___mcc_h27_ = source37_.minOperands
            d_523___mcc_h28_ = source37_.pushes
            d_524___mcc_h29_ = source37_.pops
            d_525_pops_ = d_524___mcc_h29_
            d_526_pushes_ = d_523___mcc_h28_
            if ((d_526_pushes_) == (1)) and ((d_525_pops_) == (0)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda9_(d_528_pos_):
                        return (d_528_pos_) - (1)

                    d_527_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda9_)
                    return WeakPre.Cond_StCond(d_527_shiftByOne_, (c).TrackedVals())
            elif ((d_526_pushes_) == (1)) and ((d_525_pops_) == (1)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
            elif True:
                def lambda10_(d_530_pops_, d_531_pushes_):
                    def lambda11_(d_532_pos_):
                        return ((d_532_pos_) + (d_530_pops_)) - (d_531_pushes_)

                    return lambda11_

                d_529_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda10_(d_525_pops_, d_526_pushes_))
                return WeakPre.Cond_StCond(d_529_shiftBy_, (c).TrackedVals())
        elif source37_.is_MemOp:
            d_533___mcc_h30_ = source37_.name
            d_534___mcc_h31_ = source37_.opcode
            d_535___mcc_h32_ = source37_.minCapacity
            d_536___mcc_h33_ = source37_.minOperands
            d_537___mcc_h34_ = source37_.pushes
            d_538___mcc_h35_ = source37_.pops
            d_539_pops_ = d_538___mcc_h35_
            d_540_pushes_ = d_537___mcc_h34_
            if (d_540_pushes_) == (0):
                def lambda12_(d_542_pos_):
                    return (d_542_pos_) + (2)

                d_541_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda12_)
                return WeakPre.Cond_StCond(d_541_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source37_.is_StorageOp:
            d_543___mcc_h36_ = source37_.name
            d_544___mcc_h37_ = source37_.opcode
            d_545___mcc_h38_ = source37_.minCapacity
            d_546___mcc_h39_ = source37_.minOperands
            d_547___mcc_h40_ = source37_.pushes
            d_548___mcc_h41_ = source37_.pops
            d_549_pops_ = d_548___mcc_h41_
            d_550_pushes_ = d_547___mcc_h40_
            if (d_550_pushes_) == (0):
                def lambda13_(d_552_pos_):
                    return (d_552_pos_) + (2)

                d_551_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda13_)
                return WeakPre.Cond_StCond(d_551_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source37_.is_JumpOp:
            d_553___mcc_h42_ = source37_.name
            d_554___mcc_h43_ = source37_.opcode
            d_555___mcc_h44_ = source37_.minCapacity
            d_556___mcc_h45_ = source37_.minOperands
            d_557___mcc_h46_ = source37_.pushes
            d_558___mcc_h47_ = source37_.pops
            d_559_opcode_ = d_554___mcc_h43_
            if (d_559_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_559_opcode_)) and ((d_559_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_560_k_ = ((d_559_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda14_(d_562_k_):
                    def lambda15_(d_563_pos_):
                        return (d_563_pos_) + (d_562_k_)

                    return lambda15_

                d_561_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda14_(d_560_k_))
                return WeakPre.Cond_StCond(d_561_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source37_.is_RunOp:
            d_564___mcc_h48_ = source37_.name
            d_565___mcc_h49_ = source37_.opcode
            d_566___mcc_h50_ = source37_.minCapacity
            d_567___mcc_h51_ = source37_.minOperands
            d_568___mcc_h52_ = source37_.pushes
            d_569___mcc_h53_ = source37_.pops
            d_570_opcode_ = d_565___mcc_h49_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda16_(d_572_pos_):
                    return (d_572_pos_) - (1)

                d_571_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                return WeakPre.Cond_StCond(d_571_shiftByOne_, (c).TrackedVals())
        elif source37_.is_StackOp:
            d_573___mcc_h54_ = source37_.name
            d_574___mcc_h55_ = source37_.opcode
            d_575___mcc_h56_ = source37_.minCapacity
            d_576___mcc_h57_ = source37_.minOperands
            d_577___mcc_h58_ = source37_.pushes
            d_578___mcc_h59_ = source37_.pops
            d_579_opcode_ = d_574___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_579_opcode_)) and ((d_579_opcode_) <= (EVMConstants.default__.PUSH32)):
                source38_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source38_.is_None:
                    def lambda17_(d_581_pos_):
                        return (d_581_pos_) - (1)

                    d_580_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda17_)
                    return WeakPre.Cond_StCond(d_580_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_582___mcc_h72_ = source38_.v
                    d_583_i_ = d_582___mcc_h72_
                    d_584_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_585___v142_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_583_i_)) == ((d_584_argVal_).Extract()):
                        d_586_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_583_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_583_i_) + (1)::]))
                        if (len(d_586_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda18_(d_588_pos_):
                                return (d_588_pos_) - (1)

                            d_587_shiftByMinusOne_ = MiscTypes.default__.Map(d_586_filtered_, lambda18_)
                            return WeakPre.Cond_StCond(d_587_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_583_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_583_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_579_opcode_)) and ((d_579_opcode_) <= (EVMConstants.default__.DUP16)):
                source39_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source39_.is_None:
                    def lambda19_(d_590_pos_):
                        return (d_590_pos_) - (1)

                    d_589_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda19_)
                    return WeakPre.Cond_StCond(d_589_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_591___mcc_h73_ = source39_.v
                    d_592_index0_ = d_591___mcc_h73_
                    source40_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_579_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source40_.is_None:
                        def lambda20_(d_594_opcode_):
                            def lambda21_(d_595_pos_):
                                return ((d_594_opcode_) - (EVMConstants.default__.DUP1) if (d_595_pos_) == (0) else (d_595_pos_) - (1))

                            return lambda21_

                        d_593_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda20_(d_579_opcode_))
                        return WeakPre.Cond_StCond(d_593_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_596___mcc_h74_ = source40_.v
                        d_597_index_ = d_596___mcc_h74_
                        if ((c).TrackedValAt(d_592_index0_)) == ((c).TrackedValAt(d_597_index_)):
                            d_598_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_592_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_592_index0_) + (1)::]))
                            def lambda22_(d_600_pos_):
                                return (d_600_pos_) - (1)

                            d_599_shiftByMinusOne_ = MiscTypes.default__.Map(d_598_filtered_, lambda22_)
                            return WeakPre.Cond_StCond(d_599_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_592_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_592_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_579_opcode_)) and ((d_579_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_601_k_ = ((d_579_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda23_(d_603_k_):
                    def lambda24_(d_604_pos_):
                        return (d_603_k_ if (d_604_pos_) == (0) else (0 if (d_604_pos_) == (d_603_k_) else d_604_pos_))

                    return lambda24_

                d_602_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda23_(d_601_k_))
                return WeakPre.Cond_StCond(d_602_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda25_(d_606_i_):
                    return (d_606_i_) + (1)

                d_605_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda25_)
                return WeakPre.Cond_StCond(d_605_shiftByOne_, (c).TrackedVals())
        elif source37_.is_LogOp:
            d_607___mcc_h60_ = source37_.name
            d_608___mcc_h61_ = source37_.opcode
            d_609___mcc_h62_ = source37_.minCapacity
            d_610___mcc_h63_ = source37_.minOperands
            d_611___mcc_h64_ = source37_.pushes
            d_612___mcc_h65_ = source37_.pops
            d_613_pops_ = d_612___mcc_h65_
            d_614_pushes_ = d_611___mcc_h64_
            d_615_opcode_ = d_608___mcc_h61_
            def lambda26_(d_617_pops_):
                def lambda27_(d_618_pos_):
                    return (d_618_pos_) + (d_617_pops_)

                return lambda27_

            d_616_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda26_(d_613_pops_))
            return WeakPre.Cond_StCond(d_616_shiftBy_, (c).TrackedVals())
        elif True:
            d_619___mcc_h66_ = source37_.name
            d_620___mcc_h67_ = source37_.opcode
            d_621___mcc_h68_ = source37_.minCapacity
            d_622___mcc_h69_ = source37_.minOperands
            d_623___mcc_h70_ = source37_.pushes
            d_624___mcc_h71_ = source37_.pops
            d_625_pops_ = d_624___mcc_h71_
            d_626_pushes_ = d_623___mcc_h70_
            d_627_opcode_ = d_620___mcc_h67_
            if (d_626_pushes_) == (0):
                def lambda28_(d_629_pops_):
                    def lambda29_(d_630_pos_):
                        return (d_630_pos_) + (d_629_pops_)

                    return lambda29_

                d_628_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda28_(d_625_pops_))
                return WeakPre.Cond_StCond(d_628_shiftBy_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda30_(d_632_pops_):
                        def lambda31_(d_633_pos_):
                            return (d_633_pos_) + (d_632_pops_)

                        return lambda31_

                    d_631_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda30_(d_625_pops_))
                    return WeakPre.Cond_StCond(d_631_shiftBy_, (c).TrackedVals())


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

