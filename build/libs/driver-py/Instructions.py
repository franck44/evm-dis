import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes
import Int
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
        d_188_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_189___v149_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_188_pad_) + (xc))).Extract()

    @staticmethod
    def Colours(i):
        source33_ = (i).op
        if source33_.is_ArithOp:
            d_190___mcc_h0_ = source33_.name
            d_191___mcc_h1_ = source33_.opcode
            d_192___mcc_h2_ = source33_.minCapacity
            d_193___mcc_h3_ = source33_.minOperands
            d_194___mcc_h4_ = source33_.pushes
            d_195___mcc_h5_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#316152")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#c6eb76")))
        elif source33_.is_CompOp:
            d_196___mcc_h6_ = source33_.name
            d_197___mcc_h7_ = source33_.opcode
            d_198___mcc_h8_ = source33_.minCapacity
            d_199___mcc_h9_ = source33_.minOperands
            d_200___mcc_h10_ = source33_.pushes
            d_201___mcc_h11_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkgoldenrod")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "bisque")))
        elif source33_.is_BitwiseOp:
            d_202___mcc_h12_ = source33_.name
            d_203___mcc_h13_ = source33_.opcode
            d_204___mcc_h14_ = source33_.minCapacity
            d_205___mcc_h15_ = source33_.minOperands
            d_206___mcc_h16_ = source33_.pushes
            d_207___mcc_h17_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "orange")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#f3f383")))
        elif source33_.is_KeccakOp:
            d_208___mcc_h18_ = source33_.name
            d_209___mcc_h19_ = source33_.opcode
            d_210___mcc_h20_ = source33_.minCapacity
            d_211___mcc_h21_ = source33_.minOperands
            d_212___mcc_h22_ = source33_.pushes
            d_213___mcc_h23_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "grey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "linen")))
        elif source33_.is_EnvOp:
            d_214___mcc_h24_ = source33_.name
            d_215___mcc_h25_ = source33_.opcode
            d_216___mcc_h26_ = source33_.minCapacity
            d_217___mcc_h27_ = source33_.minOperands
            d_218___mcc_h28_ = source33_.pushes
            d_219___mcc_h29_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkslategrey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightgrey")))
        elif source33_.is_MemOp:
            d_220___mcc_h30_ = source33_.name
            d_221___mcc_h31_ = source33_.opcode
            d_222___mcc_h32_ = source33_.minCapacity
            d_223___mcc_h33_ = source33_.minOperands
            d_224___mcc_h34_ = source33_.pushes
            d_225___mcc_h35_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "wheat")))
        elif source33_.is_StorageOp:
            d_226___mcc_h36_ = source33_.name
            d_227___mcc_h37_ = source33_.opcode
            d_228___mcc_h38_ = source33_.minCapacity
            d_229___mcc_h39_ = source33_.minOperands
            d_230___mcc_h40_ = source33_.pushes
            d_231___mcc_h41_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "fuchsia")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "mistyrose")))
        elif source33_.is_JumpOp:
            d_232___mcc_h42_ = source33_.name
            d_233___mcc_h43_ = source33_.opcode
            d_234___mcc_h44_ = source33_.minCapacity
            d_235___mcc_h45_ = source33_.minOperands
            d_236___mcc_h46_ = source33_.pushes
            d_237___mcc_h47_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "purple")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "thistle")))
        elif source33_.is_RunOp:
            d_238___mcc_h48_ = source33_.name
            d_239___mcc_h49_ = source33_.opcode
            d_240___mcc_h50_ = source33_.minCapacity
            d_241___mcc_h51_ = source33_.minOperands
            d_242___mcc_h52_ = source33_.pushes
            d_243___mcc_h53_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tan")))
        elif source33_.is_StackOp:
            d_244___mcc_h54_ = source33_.name
            d_245___mcc_h55_ = source33_.opcode
            d_246___mcc_h56_ = source33_.minCapacity
            d_247___mcc_h57_ = source33_.minOperands
            d_248___mcc_h58_ = source33_.pushes
            d_249___mcc_h59_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "royalblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "powderblue")))
        elif source33_.is_LogOp:
            d_250___mcc_h60_ = source33_.name
            d_251___mcc_h61_ = source33_.opcode
            d_252___mcc_h62_ = source33_.minCapacity
            d_253___mcc_h63_ = source33_.minOperands
            d_254___mcc_h64_ = source33_.pushes
            d_255___mcc_h65_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "cornflowerblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lavender")))
        elif True:
            d_256___mcc_h66_ = source33_.name
            d_257___mcc_h67_ = source33_.opcode
            d_258___mcc_h68_ = source33_.minCapacity
            d_259___mcc_h69_ = source33_.minOperands
            d_260___mcc_h70_ = source33_.pushes
            d_261___mcc_h71_ = source33_.pops
            d_262_opcode_ = d_257___mcc_h67_
            if ((d_262_opcode_) == (EVMConstants.default__.STOP)) or ((d_262_opcode_) == (EVMConstants.default__.REVERT)):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "brown")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightsalmon")))
            elif (d_262_opcode_) == (EVMConstants.default__.RETURN):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "teal")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "greenyellow")))
            elif ((((d_262_opcode_) == (EVMConstants.default__.CALL)) or ((d_262_opcode_) == (EVMConstants.default__.CALLCODE))) or ((d_262_opcode_) == (EVMConstants.default__.DELEGATECALL))) or ((d_262_opcode_) == (EVMConstants.default__.STATICCALL)):
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
        def lambda3_(forall_var_3_):
            d_263_k_: int = forall_var_3_
            return not (((0) <= (d_263_k_)) and ((d_263_k_) < (len((self).arg)))) or (Hex.default__.IsHex(((self).arg)[d_263_k_]))

        return ((((self).op).opcode) == (EVMConstants.default__.INVALID)) or ((not (((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32))) or (((len((self).arg)) == ((2) * ((((self).op).opcode) - (EVMConstants.default__.PUSH0)))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((self).arg)), True, lambda3_)))) and (not (not(((EVMConstants.default__.PUSH0) <= (((self).op).opcode)) and ((((self).op).opcode) <= (EVMConstants.default__.PUSH32)))) or ((len((self).arg)) == (0))))

    def Size(self):
        return (1) + (_dafny.euclidian_division(len((self).arg), 2))

    def ToString(self):
        d_264_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_264_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_264_x_) if (len(d_264_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def Equiv(self, i):
        return (((self).op) == ((i).op)) and (((self).arg) == ((i).arg))

    def ToHTML(self):
        d_265_x_ = (self).arg
        d_266_cols_ = default__.Colours(self)
        d_267_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_268___v0_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_269_insText_ = (((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_266_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_265_x_) if (((self).op).opcode) == (EVMConstants.default__.INVALID) else (((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_266_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_265_x_) if (len(d_265_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))))
        return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (d_267_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":")))) + (d_269_insText_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))

    def ToHTMLTable(self, entryPortTag, exitPortTag):
        d_270_cols_ = default__.Colours(self)
        d_271_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_272___v1_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_273_gasLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981;"))
        d_274_oplineTD_ = ((((((((((((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" "))) + (entryPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x")))) + (d_271_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " </TD>\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: ")))) + (EVMToolTips.default__.Gas(((self).op).opcode))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " \" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "target=\"_blank\" href=\"")))) + (EVMToolTips.default__.gasRefLine)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (d_273_gasLine_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")))) + ((d_270_cols_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" align=\"left\" cellpadding=\"3\" ")))) + (exitPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"")))) + (EVMToolTips.default__.bytecodeRefLine)) + (Int.default__.NatToString((EVMToolTips.default__.ToolTip(((self).op).opcode))[1]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" target=\"_blank\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " tooltip=\"")))) + ((EVMToolTips.default__.ToolTip(((self).op).opcode))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\"")))) + ((d_270_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))
        d_275_arglineTD_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" align=\"left\">"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  0x")))) + ((self).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>"))) if (len((self).arg)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_276_lineTR_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR>"))) + (d_274_oplineTD_)) + (d_275_arglineTD_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR>")))
        d_277_itemTable_ = ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE  border=\"0\" cellpadding=\"0\" cellborder=\"0\" CELLSPACING=\"1\">"))) + (d_276_lineTR_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>")))
        return d_277_itemTable_

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
        source34_ = (self).op
        if source34_.is_ArithOp:
            d_278___mcc_h0_ = source34_.name
            d_279___mcc_h1_ = source34_.opcode
            d_280___mcc_h2_ = source34_.minCapacity
            d_281___mcc_h3_ = source34_.minOperands
            d_282___mcc_h4_ = source34_.pushes
            d_283___mcc_h5_ = source34_.pops
            d_284_pops_ = d_283___mcc_h5_
            d_285_pushes_ = d_282___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source34_.is_CompOp:
            d_286___mcc_h6_ = source34_.name
            d_287___mcc_h7_ = source34_.opcode
            d_288___mcc_h8_ = source34_.minCapacity
            d_289___mcc_h9_ = source34_.minOperands
            d_290___mcc_h10_ = source34_.pushes
            d_291___mcc_h11_ = source34_.pops
            d_292_pops_ = d_291___mcc_h11_
            d_293_pushes_ = d_290___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_292_pops_)) - (d_293_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source34_.is_BitwiseOp:
            d_294___mcc_h12_ = source34_.name
            d_295___mcc_h13_ = source34_.opcode
            d_296___mcc_h14_ = source34_.minCapacity
            d_297___mcc_h15_ = source34_.minOperands
            d_298___mcc_h16_ = source34_.pushes
            d_299___mcc_h17_ = source34_.pops
            d_300_pops_ = d_299___mcc_h17_
            d_301_pushes_ = d_298___mcc_h16_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_300_pops_)) - (d_301_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Bitwise operator with target 0"))))
        elif source34_.is_KeccakOp:
            d_302___mcc_h18_ = source34_.name
            d_303___mcc_h19_ = source34_.opcode
            d_304___mcc_h20_ = source34_.minCapacity
            d_305___mcc_h21_ = source34_.minOperands
            d_306___mcc_h22_ = source34_.pushes
            d_307___mcc_h23_ = source34_.pops
            d_308_pops_ = d_307___mcc_h23_
            d_309_pushes_ = d_306___mcc_h22_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Keccak operator with target 0"))))
        elif source34_.is_EnvOp:
            d_310___mcc_h24_ = source34_.name
            d_311___mcc_h25_ = source34_.opcode
            d_312___mcc_h26_ = source34_.minCapacity
            d_313___mcc_h27_ = source34_.minOperands
            d_314___mcc_h28_ = source34_.pushes
            d_315___mcc_h29_ = source34_.pops
            d_316_pops_ = d_315___mcc_h29_
            d_317_pushes_ = d_314___mcc_h28_
            if ((d_317_pushes_) == (1)) and ((d_316_pops_) == (0)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((d_317_pushes_) == (1)) and ((d_316_pops_) == (1)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
            elif True:
                return MiscTypes.Either_Right(((pos_k) + (d_316_pops_)) - (d_317_pushes_))
        elif source34_.is_MemOp:
            d_318___mcc_h30_ = source34_.name
            d_319___mcc_h31_ = source34_.opcode
            d_320___mcc_h32_ = source34_.minCapacity
            d_321___mcc_h33_ = source34_.minOperands
            d_322___mcc_h34_ = source34_.pushes
            d_323___mcc_h35_ = source34_.pops
            d_324_pops_ = d_323___mcc_h35_
            d_325_pushes_ = d_322___mcc_h34_
            if (d_325_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Mem operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source34_.is_StorageOp:
            d_326___mcc_h36_ = source34_.name
            d_327___mcc_h37_ = source34_.opcode
            d_328___mcc_h38_ = source34_.minCapacity
            d_329___mcc_h39_ = source34_.minOperands
            d_330___mcc_h40_ = source34_.pushes
            d_331___mcc_h41_ = source34_.pops
            d_332_pops_ = d_331___mcc_h41_
            d_333_pushes_ = d_330___mcc_h40_
            if (d_333_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Storage operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source34_.is_JumpOp:
            d_334___mcc_h42_ = source34_.name
            d_335___mcc_h43_ = source34_.opcode
            d_336___mcc_h44_ = source34_.minCapacity
            d_337___mcc_h45_ = source34_.minOperands
            d_338___mcc_h46_ = source34_.pushes
            d_339___mcc_h47_ = source34_.pops
            d_340_opcode_ = d_335___mcc_h43_
            if (d_340_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_340_opcode_)) and ((d_340_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_341_k_ = ((d_340_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_341_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source34_.is_RunOp:
            d_342___mcc_h48_ = source34_.name
            d_343___mcc_h49_ = source34_.opcode
            d_344___mcc_h50_ = source34_.minCapacity
            d_345___mcc_h51_ = source34_.minOperands
            d_346___mcc_h52_ = source34_.pushes
            d_347___mcc_h53_ = source34_.pops
            d_348_pops_ = d_347___mcc_h53_
            d_349_pushes_ = d_346___mcc_h52_
            if (pos_k) == (0):
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Run operator with target 0"))))
            elif True:
                return MiscTypes.Either_Right((pos_k) - (1))
        elif source34_.is_StackOp:
            d_350___mcc_h54_ = source34_.name
            d_351___mcc_h55_ = source34_.opcode
            d_352___mcc_h56_ = source34_.minCapacity
            d_353___mcc_h57_ = source34_.minOperands
            d_354___mcc_h58_ = source34_.pushes
            d_355___mcc_h59_ = source34_.pops
            d_356_opcode_ = d_351___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_356_opcode_)) and ((d_356_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_356_opcode_)) and ((d_356_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_356_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_356_opcode_)) and ((d_356_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_357_k_ = ((d_356_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_357_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_357_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source34_.is_LogOp:
            d_358___mcc_h60_ = source34_.name
            d_359___mcc_h61_ = source34_.opcode
            d_360___mcc_h62_ = source34_.minCapacity
            d_361___mcc_h63_ = source34_.minOperands
            d_362___mcc_h64_ = source34_.pushes
            d_363___mcc_h65_ = source34_.pops
            d_364_pops_ = d_363___mcc_h65_
            d_365_pushes_ = d_362___mcc_h64_
            return MiscTypes.Either_Right((pos_k) + (d_364_pops_))
        elif True:
            d_366___mcc_h66_ = source34_.name
            d_367___mcc_h67_ = source34_.opcode
            d_368___mcc_h68_ = source34_.minCapacity
            d_369___mcc_h69_ = source34_.minOperands
            d_370___mcc_h70_ = source34_.pushes
            d_371___mcc_h71_ = source34_.pops
            d_372_pops_ = d_371___mcc_h71_
            d_373_pushes_ = d_370___mcc_h70_
            if (d_373_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (d_372_pops_))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Sys operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) + (d_372_pops_))

    def NextState(self, s, jumpDests, cond):
        source35_ = (self).op
        if source35_.is_ArithOp:
            d_374___mcc_h0_ = source35_.name
            d_375___mcc_h1_ = source35_.opcode
            d_376___mcc_h2_ = source35_.minCapacity
            d_377___mcc_h3_ = source35_.minOperands
            d_378___mcc_h4_ = source35_.pushes
            d_379___mcc_h5_ = source35_.pops
            d_380_pops_ = d_379___mcc_h5_
            d_381_pushes_ = d_378___mcc_h4_
            if (((s).Size()) >= (d_380_pops_)) and (not(cond)):
                return (((s).PopN(d_380_pops_)).PushNRandom(d_381_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_CompOp:
            d_382___mcc_h6_ = source35_.name
            d_383___mcc_h7_ = source35_.opcode
            d_384___mcc_h8_ = source35_.minCapacity
            d_385___mcc_h9_ = source35_.minOperands
            d_386___mcc_h10_ = source35_.pushes
            d_387___mcc_h11_ = source35_.pops
            d_388_pops_ = d_387___mcc_h11_
            d_389_pushes_ = d_386___mcc_h10_
            if (((s).Size()) >= (d_388_pops_)) and (not(cond)):
                return (((s).PopN(d_388_pops_)).PushNRandom(d_389_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_BitwiseOp:
            d_390___mcc_h12_ = source35_.name
            d_391___mcc_h13_ = source35_.opcode
            d_392___mcc_h14_ = source35_.minCapacity
            d_393___mcc_h15_ = source35_.minOperands
            d_394___mcc_h16_ = source35_.pushes
            d_395___mcc_h17_ = source35_.pops
            d_396_pops_ = d_395___mcc_h17_
            d_397_pushes_ = d_394___mcc_h16_
            if (((s).Size()) >= (d_396_pops_)) and (not(cond)):
                return (((s).PopN(d_396_pops_)).PushNRandom(d_397_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_KeccakOp:
            d_398___mcc_h18_ = source35_.name
            d_399___mcc_h19_ = source35_.opcode
            d_400___mcc_h20_ = source35_.minCapacity
            d_401___mcc_h21_ = source35_.minOperands
            d_402___mcc_h22_ = source35_.pushes
            d_403___mcc_h23_ = source35_.pops
            d_404_pops_ = d_403___mcc_h23_
            d_405_pushes_ = d_402___mcc_h22_
            if (((s).Size()) >= (2)) and (not(cond)):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_EnvOp:
            d_406___mcc_h24_ = source35_.name
            d_407___mcc_h25_ = source35_.opcode
            d_408___mcc_h26_ = source35_.minCapacity
            d_409___mcc_h27_ = source35_.minOperands
            d_410___mcc_h28_ = source35_.pushes
            d_411___mcc_h29_ = source35_.pops
            d_412_pops_ = d_411___mcc_h29_
            d_413_pushes_ = d_410___mcc_h28_
            if (((s).Size()) >= (d_412_pops_)) and (not(cond)):
                return (((s).PopN(d_412_pops_)).PushNRandom(d_413_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        elif source35_.is_MemOp:
            d_414___mcc_h30_ = source35_.name
            d_415___mcc_h31_ = source35_.opcode
            d_416___mcc_h32_ = source35_.minCapacity
            d_417___mcc_h33_ = source35_.minOperands
            d_418___mcc_h34_ = source35_.pushes
            d_419___mcc_h35_ = source35_.pops
            d_420_pops_ = d_419___mcc_h35_
            d_421_pushes_ = d_418___mcc_h34_
            if (((s).Size()) >= (d_420_pops_)) and (not(cond)):
                return (((s).PopN(d_420_pops_)).PushNRandom(d_421_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        elif source35_.is_StorageOp:
            d_422___mcc_h36_ = source35_.name
            d_423___mcc_h37_ = source35_.opcode
            d_424___mcc_h38_ = source35_.minCapacity
            d_425___mcc_h39_ = source35_.minOperands
            d_426___mcc_h40_ = source35_.pushes
            d_427___mcc_h41_ = source35_.pops
            d_428_pops_ = d_427___mcc_h41_
            d_429_pushes_ = d_426___mcc_h40_
            if (((s).Size()) >= (d_428_pops_)) and (not(cond)):
                return (((s).PopN(d_428_pops_)).PushNRandom(d_429_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        elif source35_.is_JumpOp:
            d_430___mcc_h42_ = source35_.name
            d_431___mcc_h43_ = source35_.opcode
            d_432___mcc_h44_ = source35_.minCapacity
            d_433___mcc_h45_ = source35_.minOperands
            d_434___mcc_h46_ = source35_.pushes
            d_435___mcc_h47_ = source35_.pops
            d_436_pops_ = d_435___mcc_h47_
            d_437_pushes_ = d_434___mcc_h46_
            d_438_opcode_ = d_431___mcc_h43_
            if (d_438_opcode_) == (EVMConstants.default__.JUMPDEST):
                if not(cond):
                    return (s).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPDEST/exit true")))
            elif (d_438_opcode_) == (EVMConstants.default__.JUMP):
                if (((s).Size()) >= (1)) and (cond):
                    source36_ = (s).Peek(0)
                    if source36_.is_Value:
                        d_439___mcc_h72_ = source36_.v
                        d_440_v_ = d_439___mcc_h72_
                        return ((s).Pop()).Goto(d_440_v_)
                    elif True:
                        d_441___mcc_h73_ = source36_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_438_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source37_ = (s).Peek(0)
                    if source37_.is_Value:
                        d_442___mcc_h74_ = source37_.v
                        d_443_v_ = d_442___mcc_h74_
                        if cond:
                            return ((s).PopN(2)).Goto(d_443_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_444___mcc_h75_ = source37_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source35_.is_RunOp:
            d_445___mcc_h48_ = source35_.name
            d_446___mcc_h49_ = source35_.opcode
            d_447___mcc_h50_ = source35_.minCapacity
            d_448___mcc_h51_ = source35_.minOperands
            d_449___mcc_h52_ = source35_.pushes
            d_450___mcc_h53_ = source35_.pops
            d_451_pops_ = d_450___mcc_h53_
            d_452_pushes_ = d_449___mcc_h52_
            if not(cond):
                return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RunOp error")))
        elif source35_.is_StackOp:
            d_453___mcc_h54_ = source35_.name
            d_454___mcc_h55_ = source35_.opcode
            d_455___mcc_h56_ = source35_.minCapacity
            d_456___mcc_h57_ = source35_.minOperands
            d_457___mcc_h58_ = source35_.pushes
            d_458___mcc_h59_ = source35_.pops
            d_459_pops_ = d_458___mcc_h59_
            d_460_pushes_ = d_457___mcc_h58_
            d_461_opcode_ = d_454___mcc_h55_
            if (((d_461_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1))) and (not(cond)):
                return ((s).Pop()).Skip(1)
            elif (((EVMConstants.default__.PUSH0) <= (d_461_opcode_)) and ((d_461_opcode_) <= (EVMConstants.default__.PUSH32))) and (not(cond)):
                d_462_valToPush_ = (StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)) if (default__.GetArgValuePush((self).arg)) in (jumpDests) else StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))
                return ((s).Push(d_462_valToPush_)).Skip((1) + ((d_461_opcode_) - (EVMConstants.default__.PUSH0)))
            elif ((((EVMConstants.default__.DUP1) <= (d_461_opcode_)) and ((d_461_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_461_opcode_) - (EVMConstants.default__.DUP1)) + (1)))) and (not(cond)):
                return ((s).Dup(((d_461_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif ((((EVMConstants.default__.SWAP1) <= (d_461_opcode_)) and ((d_461_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_461_opcode_) - (EVMConstants.default__.SWAP1)) + (1)))) and (not(cond)):
                return ((s).Swap(((d_461_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        elif source35_.is_LogOp:
            d_463___mcc_h60_ = source35_.name
            d_464___mcc_h61_ = source35_.opcode
            d_465___mcc_h62_ = source35_.minCapacity
            d_466___mcc_h63_ = source35_.minOperands
            d_467___mcc_h64_ = source35_.pushes
            d_468___mcc_h65_ = source35_.pops
            d_469_pops_ = d_468___mcc_h65_
            d_470_pushes_ = d_467___mcc_h64_
            if (((s).Size()) >= (d_469_pops_)) and (not(cond)):
                return ((s).PopN(d_469_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        elif True:
            d_471___mcc_h66_ = source35_.name
            d_472___mcc_h67_ = source35_.opcode
            d_473___mcc_h68_ = source35_.minCapacity
            d_474___mcc_h69_ = source35_.minOperands
            d_475___mcc_h70_ = source35_.pushes
            d_476___mcc_h71_ = source35_.pops
            d_477_pops_ = d_476___mcc_h71_
            d_478_pushes_ = d_475___mcc_h70_
            d_479_op_ = d_472___mcc_h67_
            if (((d_479_op_) == (EVMConstants.default__.INVALID)) or ((d_479_op_) == (EVMConstants.default__.STOP))) or ((d_479_op_) == (EVMConstants.default__.REVERT)):
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))
            elif (((s).Size()) >= (d_477_pops_)) and (not(cond)):
                return (((s).PopN(d_477_pops_)).PushNRandom(d_478_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source38_ = (self).op
        if source38_.is_ArithOp:
            d_480___mcc_h0_ = source38_.name
            d_481___mcc_h1_ = source38_.opcode
            d_482___mcc_h2_ = source38_.minCapacity
            d_483___mcc_h3_ = source38_.minOperands
            d_484___mcc_h4_ = source38_.pushes
            d_485___mcc_h5_ = source38_.pops
            d_486_pops_ = d_485___mcc_h5_
            d_487_pushes_ = d_484___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda4_(d_489_pos_):
                    return (d_489_pos_) + (1)

                d_488_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda4_)
                return WeakPre.Cond_StCond(d_488_shiftByOne_, (c).TrackedVals())
        elif source38_.is_CompOp:
            d_490___mcc_h6_ = source38_.name
            d_491___mcc_h7_ = source38_.opcode
            d_492___mcc_h8_ = source38_.minCapacity
            d_493___mcc_h9_ = source38_.minOperands
            d_494___mcc_h10_ = source38_.pushes
            d_495___mcc_h11_ = source38_.pops
            d_496_pops_ = d_495___mcc_h11_
            d_497_pushes_ = d_494___mcc_h10_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda5_(d_499_pops_, d_500_pushes_):
                    def lambda6_(d_501_pos_):
                        return ((d_501_pos_) + (d_499_pops_)) - (d_500_pushes_)

                    return lambda6_

                d_498_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda5_(d_496_pops_, d_497_pushes_))
                return WeakPre.Cond_StCond(d_498_shiftBy_, (c).TrackedVals())
        elif source38_.is_BitwiseOp:
            d_502___mcc_h12_ = source38_.name
            d_503___mcc_h13_ = source38_.opcode
            d_504___mcc_h14_ = source38_.minCapacity
            d_505___mcc_h15_ = source38_.minOperands
            d_506___mcc_h16_ = source38_.pushes
            d_507___mcc_h17_ = source38_.pops
            d_508_pops_ = d_507___mcc_h17_
            d_509_pushes_ = d_506___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda7_(d_511_pops_, d_512_pushes_):
                    def lambda8_(d_513_pos_):
                        return ((d_513_pos_) + (d_511_pops_)) - (d_512_pushes_)

                    return lambda8_

                d_510_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda7_(d_508_pops_, d_509_pushes_))
                return WeakPre.Cond_StCond(d_510_shiftBy_, (c).TrackedVals())
        elif source38_.is_KeccakOp:
            d_514___mcc_h18_ = source38_.name
            d_515___mcc_h19_ = source38_.opcode
            d_516___mcc_h20_ = source38_.minCapacity
            d_517___mcc_h21_ = source38_.minOperands
            d_518___mcc_h22_ = source38_.pushes
            d_519___mcc_h23_ = source38_.pops
            d_520_pops_ = d_519___mcc_h23_
            d_521_pushes_ = d_518___mcc_h22_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda9_(d_523_pos_):
                    return (d_523_pos_) + (1)

                d_522_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda9_)
                return WeakPre.Cond_StCond(d_522_shiftByOne_, (c).TrackedVals())
        elif source38_.is_EnvOp:
            d_524___mcc_h24_ = source38_.name
            d_525___mcc_h25_ = source38_.opcode
            d_526___mcc_h26_ = source38_.minCapacity
            d_527___mcc_h27_ = source38_.minOperands
            d_528___mcc_h28_ = source38_.pushes
            d_529___mcc_h29_ = source38_.pops
            d_530_pops_ = d_529___mcc_h29_
            d_531_pushes_ = d_528___mcc_h28_
            if ((d_531_pushes_) == (1)) and ((d_530_pops_) == (0)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda10_(d_533_pos_):
                        return (d_533_pos_) - (1)

                    d_532_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda10_)
                    return WeakPre.Cond_StCond(d_532_shiftByOne_, (c).TrackedVals())
            elif ((d_531_pushes_) == (1)) and ((d_530_pops_) == (1)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
            elif True:
                def lambda11_(d_535_pops_, d_536_pushes_):
                    def lambda12_(d_537_pos_):
                        return ((d_537_pos_) + (d_535_pops_)) - (d_536_pushes_)

                    return lambda12_

                d_534_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda11_(d_530_pops_, d_531_pushes_))
                return WeakPre.Cond_StCond(d_534_shiftBy_, (c).TrackedVals())
        elif source38_.is_MemOp:
            d_538___mcc_h30_ = source38_.name
            d_539___mcc_h31_ = source38_.opcode
            d_540___mcc_h32_ = source38_.minCapacity
            d_541___mcc_h33_ = source38_.minOperands
            d_542___mcc_h34_ = source38_.pushes
            d_543___mcc_h35_ = source38_.pops
            d_544_pops_ = d_543___mcc_h35_
            d_545_pushes_ = d_542___mcc_h34_
            if (d_545_pushes_) == (0):
                def lambda13_(d_547_pos_):
                    return (d_547_pos_) + (2)

                d_546_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda13_)
                return WeakPre.Cond_StCond(d_546_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source38_.is_StorageOp:
            d_548___mcc_h36_ = source38_.name
            d_549___mcc_h37_ = source38_.opcode
            d_550___mcc_h38_ = source38_.minCapacity
            d_551___mcc_h39_ = source38_.minOperands
            d_552___mcc_h40_ = source38_.pushes
            d_553___mcc_h41_ = source38_.pops
            d_554_pops_ = d_553___mcc_h41_
            d_555_pushes_ = d_552___mcc_h40_
            if (d_555_pushes_) == (0):
                def lambda14_(d_557_pos_):
                    return (d_557_pos_) + (2)

                d_556_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda14_)
                return WeakPre.Cond_StCond(d_556_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source38_.is_JumpOp:
            d_558___mcc_h42_ = source38_.name
            d_559___mcc_h43_ = source38_.opcode
            d_560___mcc_h44_ = source38_.minCapacity
            d_561___mcc_h45_ = source38_.minOperands
            d_562___mcc_h46_ = source38_.pushes
            d_563___mcc_h47_ = source38_.pops
            d_564_opcode_ = d_559___mcc_h43_
            if (d_564_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_564_opcode_)) and ((d_564_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_565_k_ = ((d_564_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda15_(d_567_k_):
                    def lambda16_(d_568_pos_):
                        return (d_568_pos_) + (d_567_k_)

                    return lambda16_

                d_566_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda15_(d_565_k_))
                return WeakPre.Cond_StCond(d_566_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source38_.is_RunOp:
            d_569___mcc_h48_ = source38_.name
            d_570___mcc_h49_ = source38_.opcode
            d_571___mcc_h50_ = source38_.minCapacity
            d_572___mcc_h51_ = source38_.minOperands
            d_573___mcc_h52_ = source38_.pushes
            d_574___mcc_h53_ = source38_.pops
            d_575_opcode_ = d_570___mcc_h49_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda17_(d_577_pos_):
                    return (d_577_pos_) - (1)

                d_576_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda17_)
                return WeakPre.Cond_StCond(d_576_shiftByOne_, (c).TrackedVals())
        elif source38_.is_StackOp:
            d_578___mcc_h54_ = source38_.name
            d_579___mcc_h55_ = source38_.opcode
            d_580___mcc_h56_ = source38_.minCapacity
            d_581___mcc_h57_ = source38_.minOperands
            d_582___mcc_h58_ = source38_.pushes
            d_583___mcc_h59_ = source38_.pops
            d_584_opcode_ = d_579___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_584_opcode_)) and ((d_584_opcode_) <= (EVMConstants.default__.PUSH32)):
                source39_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source39_.is_None:
                    def lambda18_(d_586_pos_):
                        return (d_586_pos_) - (1)

                    d_585_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda18_)
                    return WeakPre.Cond_StCond(d_585_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_587___mcc_h72_ = source39_.v
                    d_588_i_ = d_587___mcc_h72_
                    d_589_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_590___v142_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_588_i_)) == ((d_589_argVal_).Extract()):
                        d_591_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_588_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_588_i_) + (1)::]))
                        if (len(d_591_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda19_(d_593_pos_):
                                return (d_593_pos_) - (1)

                            d_592_shiftByMinusOne_ = MiscTypes.default__.Map(d_591_filtered_, lambda19_)
                            return WeakPre.Cond_StCond(d_592_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_588_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_588_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_584_opcode_)) and ((d_584_opcode_) <= (EVMConstants.default__.DUP16)):
                source40_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source40_.is_None:
                    def lambda20_(d_595_pos_):
                        return (d_595_pos_) - (1)

                    d_594_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda20_)
                    return WeakPre.Cond_StCond(d_594_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_596___mcc_h73_ = source40_.v
                    d_597_index0_ = d_596___mcc_h73_
                    source41_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_584_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source41_.is_None:
                        def lambda21_(d_599_opcode_):
                            def lambda22_(d_600_pos_):
                                return ((d_599_opcode_) - (EVMConstants.default__.DUP1) if (d_600_pos_) == (0) else (d_600_pos_) - (1))

                            return lambda22_

                        d_598_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda21_(d_584_opcode_))
                        return WeakPre.Cond_StCond(d_598_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_601___mcc_h74_ = source41_.v
                        d_602_index_ = d_601___mcc_h74_
                        if ((c).TrackedValAt(d_597_index0_)) == ((c).TrackedValAt(d_602_index_)):
                            d_603_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_597_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_597_index0_) + (1)::]))
                            def lambda23_(d_605_pos_):
                                return (d_605_pos_) - (1)

                            d_604_shiftByMinusOne_ = MiscTypes.default__.Map(d_603_filtered_, lambda23_)
                            return WeakPre.Cond_StCond(d_604_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_597_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_597_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_584_opcode_)) and ((d_584_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_606_k_ = ((d_584_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda24_(d_608_k_):
                    def lambda25_(d_609_pos_):
                        return (d_608_k_ if (d_609_pos_) == (0) else (0 if (d_609_pos_) == (d_608_k_) else d_609_pos_))

                    return lambda25_

                d_607_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda24_(d_606_k_))
                return WeakPre.Cond_StCond(d_607_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda26_(d_611_i_):
                    return (d_611_i_) + (1)

                d_610_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda26_)
                return WeakPre.Cond_StCond(d_610_shiftByOne_, (c).TrackedVals())
        elif source38_.is_LogOp:
            d_612___mcc_h60_ = source38_.name
            d_613___mcc_h61_ = source38_.opcode
            d_614___mcc_h62_ = source38_.minCapacity
            d_615___mcc_h63_ = source38_.minOperands
            d_616___mcc_h64_ = source38_.pushes
            d_617___mcc_h65_ = source38_.pops
            d_618_pops_ = d_617___mcc_h65_
            d_619_pushes_ = d_616___mcc_h64_
            d_620_opcode_ = d_613___mcc_h61_
            def lambda27_(d_622_pops_):
                def lambda28_(d_623_pos_):
                    return (d_623_pos_) + (d_622_pops_)

                return lambda28_

            d_621_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda27_(d_618_pops_))
            return WeakPre.Cond_StCond(d_621_shiftBy_, (c).TrackedVals())
        elif True:
            d_624___mcc_h66_ = source38_.name
            d_625___mcc_h67_ = source38_.opcode
            d_626___mcc_h68_ = source38_.minCapacity
            d_627___mcc_h69_ = source38_.minOperands
            d_628___mcc_h70_ = source38_.pushes
            d_629___mcc_h71_ = source38_.pops
            d_630_pops_ = d_629___mcc_h71_
            d_631_pushes_ = d_628___mcc_h70_
            d_632_opcode_ = d_625___mcc_h67_
            if (d_631_pushes_) == (0):
                def lambda29_(d_634_pops_):
                    def lambda30_(d_635_pos_):
                        return (d_635_pos_) + (d_634_pops_)

                    return lambda30_

                d_633_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda29_(d_630_pops_))
                return WeakPre.Cond_StCond(d_633_shiftBy_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda31_(d_637_pops_):
                        def lambda32_(d_638_pos_):
                            return (d_638_pos_) + (d_637_pops_)

                        return lambda32_

                    d_636_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda31_(d_630_pops_))
                    return WeakPre.Cond_StCond(d_636_shiftBy_, (c).TrackedVals())


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

