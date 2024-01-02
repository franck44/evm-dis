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
        d_195_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_196___v149_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_195_pad_) + (xc))).Extract()

    @staticmethod
    def ToDot(xi):
        d_197___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_197___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_197___accumulator_ = (d_197___accumulator_) + (((xi)[0]).ToHTML())
                    in28_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in28_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Colours(i):
        source33_ = (i).op
        if source33_.is_ArithOp:
            d_198___mcc_h0_ = source33_.name
            d_199___mcc_h1_ = source33_.opcode
            d_200___mcc_h2_ = source33_.minCapacity
            d_201___mcc_h3_ = source33_.minOperands
            d_202___mcc_h4_ = source33_.pushes
            d_203___mcc_h5_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#316152")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#c6eb76")))
        elif source33_.is_CompOp:
            d_204___mcc_h6_ = source33_.name
            d_205___mcc_h7_ = source33_.opcode
            d_206___mcc_h8_ = source33_.minCapacity
            d_207___mcc_h9_ = source33_.minOperands
            d_208___mcc_h10_ = source33_.pushes
            d_209___mcc_h11_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkgoldenrod")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "bisque")))
        elif source33_.is_BitwiseOp:
            d_210___mcc_h12_ = source33_.name
            d_211___mcc_h13_ = source33_.opcode
            d_212___mcc_h14_ = source33_.minCapacity
            d_213___mcc_h15_ = source33_.minOperands
            d_214___mcc_h16_ = source33_.pushes
            d_215___mcc_h17_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "orange")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#f3f383")))
        elif source33_.is_KeccakOp:
            d_216___mcc_h18_ = source33_.name
            d_217___mcc_h19_ = source33_.opcode
            d_218___mcc_h20_ = source33_.minCapacity
            d_219___mcc_h21_ = source33_.minOperands
            d_220___mcc_h22_ = source33_.pushes
            d_221___mcc_h23_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "grey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "linen")))
        elif source33_.is_EnvOp:
            d_222___mcc_h24_ = source33_.name
            d_223___mcc_h25_ = source33_.opcode
            d_224___mcc_h26_ = source33_.minCapacity
            d_225___mcc_h27_ = source33_.minOperands
            d_226___mcc_h28_ = source33_.pushes
            d_227___mcc_h29_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkslategrey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightgrey")))
        elif source33_.is_MemOp:
            d_228___mcc_h30_ = source33_.name
            d_229___mcc_h31_ = source33_.opcode
            d_230___mcc_h32_ = source33_.minCapacity
            d_231___mcc_h33_ = source33_.minOperands
            d_232___mcc_h34_ = source33_.pushes
            d_233___mcc_h35_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "wheat")))
        elif source33_.is_StorageOp:
            d_234___mcc_h36_ = source33_.name
            d_235___mcc_h37_ = source33_.opcode
            d_236___mcc_h38_ = source33_.minCapacity
            d_237___mcc_h39_ = source33_.minOperands
            d_238___mcc_h40_ = source33_.pushes
            d_239___mcc_h41_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "fuchsia")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "mistyrose")))
        elif source33_.is_JumpOp:
            d_240___mcc_h42_ = source33_.name
            d_241___mcc_h43_ = source33_.opcode
            d_242___mcc_h44_ = source33_.minCapacity
            d_243___mcc_h45_ = source33_.minOperands
            d_244___mcc_h46_ = source33_.pushes
            d_245___mcc_h47_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "purple")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "thistle")))
        elif source33_.is_RunOp:
            d_246___mcc_h48_ = source33_.name
            d_247___mcc_h49_ = source33_.opcode
            d_248___mcc_h50_ = source33_.minCapacity
            d_249___mcc_h51_ = source33_.minOperands
            d_250___mcc_h52_ = source33_.pushes
            d_251___mcc_h53_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tan")))
        elif source33_.is_StackOp:
            d_252___mcc_h54_ = source33_.name
            d_253___mcc_h55_ = source33_.opcode
            d_254___mcc_h56_ = source33_.minCapacity
            d_255___mcc_h57_ = source33_.minOperands
            d_256___mcc_h58_ = source33_.pushes
            d_257___mcc_h59_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "royalblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "powderblue")))
        elif source33_.is_LogOp:
            d_258___mcc_h60_ = source33_.name
            d_259___mcc_h61_ = source33_.opcode
            d_260___mcc_h62_ = source33_.minCapacity
            d_261___mcc_h63_ = source33_.minOperands
            d_262___mcc_h64_ = source33_.pushes
            d_263___mcc_h65_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "cornflowerblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lavender")))
        elif True:
            d_264___mcc_h66_ = source33_.name
            d_265___mcc_h67_ = source33_.opcode
            d_266___mcc_h68_ = source33_.minCapacity
            d_267___mcc_h69_ = source33_.minOperands
            d_268___mcc_h70_ = source33_.pushes
            d_269___mcc_h71_ = source33_.pops
            d_270_opcode_ = d_265___mcc_h67_
            if ((d_270_opcode_) == (EVMConstants.default__.STOP)) or ((d_270_opcode_) == (EVMConstants.default__.REVERT)):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "brown")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightsalmon")))
            elif (d_270_opcode_) == (EVMConstants.default__.RETURN):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "teal")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "greenyellow")))
            elif ((((d_270_opcode_) == (EVMConstants.default__.CALL)) or ((d_270_opcode_) == (EVMConstants.default__.CALLCODE))) or ((d_270_opcode_) == (EVMConstants.default__.DELEGATECALL))) or ((d_270_opcode_) == (EVMConstants.default__.STATICCALL)):
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
    def Size(self):
        return (1) + (_dafny.euclidian_division(len((self).arg), 2))

    def ToString(self):
        d_271_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_271_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_271_x_) if (len(d_271_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def Equiv(self, i):
        return (((self).op) == ((i).op)) and (((self).arg) == ((i).arg))

    def ToHTML(self):
        d_272_x_ = (self).arg
        d_273_cols_ = default__.Colours(self)
        d_274_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_275___v0_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_276_insText_ = (((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_273_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_272_x_) if (((self).op).opcode) == (EVMConstants.default__.INVALID) else (((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_273_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_272_x_) if (len(d_272_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))))
        return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (d_274_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":")))) + (d_276_insText_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))

    def ToHTMLTable(self, entryPortTag, exitPortTag):
        d_277_cols_ = default__.Colours(self)
        d_278_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_279___v1_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_280_gasLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981;"))
        d_281_oplineTD_ = ((((((((((((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" "))) + (entryPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x")))) + (d_278_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " </TD>\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: ")))) + (EVMToolTips.default__.Gas(((self).op).opcode))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " \" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "target=\"_blank\" href=\"")))) + (EVMToolTips.default__.gasRefLine)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (d_280_gasLine_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")))) + ((d_277_cols_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" align=\"left\" cellpadding=\"3\" ")))) + (exitPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"")))) + (EVMToolTips.default__.bytecodeRefLine)) + (Int.default__.NatToString((EVMToolTips.default__.ToolTip(((self).op).opcode))[1]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" target=\"_blank\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " tooltip=\"")))) + ((EVMToolTips.default__.ToolTip(((self).op).opcode))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\"")))) + ((d_277_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))
        d_282_arglineTD_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" align=\"left\">"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  0x")))) + ((self).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>"))) if (len((self).arg)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_283_lineTR_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR>"))) + (d_281_oplineTD_)) + (d_282_arglineTD_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR>")))
        d_284_itemTable_ = ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE  border=\"0\" cellpadding=\"0\" cellborder=\"0\" CELLSPACING=\"1\">"))) + (d_283_lineTR_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>")))
        return d_284_itemTable_

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
            d_285___mcc_h0_ = source34_.name
            d_286___mcc_h1_ = source34_.opcode
            d_287___mcc_h2_ = source34_.minCapacity
            d_288___mcc_h3_ = source34_.minOperands
            d_289___mcc_h4_ = source34_.pushes
            d_290___mcc_h5_ = source34_.pops
            d_291_pops_ = d_290___mcc_h5_
            d_292_pushes_ = d_289___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source34_.is_CompOp:
            d_293___mcc_h6_ = source34_.name
            d_294___mcc_h7_ = source34_.opcode
            d_295___mcc_h8_ = source34_.minCapacity
            d_296___mcc_h9_ = source34_.minOperands
            d_297___mcc_h10_ = source34_.pushes
            d_298___mcc_h11_ = source34_.pops
            d_299_pops_ = d_298___mcc_h11_
            d_300_pushes_ = d_297___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_299_pops_)) - (d_300_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source34_.is_BitwiseOp:
            d_301___mcc_h12_ = source34_.name
            d_302___mcc_h13_ = source34_.opcode
            d_303___mcc_h14_ = source34_.minCapacity
            d_304___mcc_h15_ = source34_.minOperands
            d_305___mcc_h16_ = source34_.pushes
            d_306___mcc_h17_ = source34_.pops
            d_307_pops_ = d_306___mcc_h17_
            d_308_pushes_ = d_305___mcc_h16_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_307_pops_)) - (d_308_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Bitwise operator with target 0"))))
        elif source34_.is_KeccakOp:
            d_309___mcc_h18_ = source34_.name
            d_310___mcc_h19_ = source34_.opcode
            d_311___mcc_h20_ = source34_.minCapacity
            d_312___mcc_h21_ = source34_.minOperands
            d_313___mcc_h22_ = source34_.pushes
            d_314___mcc_h23_ = source34_.pops
            d_315_pops_ = d_314___mcc_h23_
            d_316_pushes_ = d_313___mcc_h22_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Keccak operator with target 0"))))
        elif source34_.is_EnvOp:
            d_317___mcc_h24_ = source34_.name
            d_318___mcc_h25_ = source34_.opcode
            d_319___mcc_h26_ = source34_.minCapacity
            d_320___mcc_h27_ = source34_.minOperands
            d_321___mcc_h28_ = source34_.pushes
            d_322___mcc_h29_ = source34_.pops
            d_323_pops_ = d_322___mcc_h29_
            d_324_pushes_ = d_321___mcc_h28_
            if ((d_324_pushes_) == (1)) and ((d_323_pops_) == (0)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((d_324_pushes_) == (1)) and ((d_323_pops_) == (1)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
            elif True:
                return MiscTypes.Either_Right(((pos_k) + (d_323_pops_)) - (d_324_pushes_))
        elif source34_.is_MemOp:
            d_325___mcc_h30_ = source34_.name
            d_326___mcc_h31_ = source34_.opcode
            d_327___mcc_h32_ = source34_.minCapacity
            d_328___mcc_h33_ = source34_.minOperands
            d_329___mcc_h34_ = source34_.pushes
            d_330___mcc_h35_ = source34_.pops
            d_331_pops_ = d_330___mcc_h35_
            d_332_pushes_ = d_329___mcc_h34_
            if (d_332_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Mem operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source34_.is_StorageOp:
            d_333___mcc_h36_ = source34_.name
            d_334___mcc_h37_ = source34_.opcode
            d_335___mcc_h38_ = source34_.minCapacity
            d_336___mcc_h39_ = source34_.minOperands
            d_337___mcc_h40_ = source34_.pushes
            d_338___mcc_h41_ = source34_.pops
            d_339_pops_ = d_338___mcc_h41_
            d_340_pushes_ = d_337___mcc_h40_
            if (d_340_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Storage operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source34_.is_JumpOp:
            d_341___mcc_h42_ = source34_.name
            d_342___mcc_h43_ = source34_.opcode
            d_343___mcc_h44_ = source34_.minCapacity
            d_344___mcc_h45_ = source34_.minOperands
            d_345___mcc_h46_ = source34_.pushes
            d_346___mcc_h47_ = source34_.pops
            d_347_opcode_ = d_342___mcc_h43_
            if (d_347_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_347_opcode_)) and ((d_347_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_348_k_ = ((d_347_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_348_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source34_.is_RunOp:
            d_349___mcc_h48_ = source34_.name
            d_350___mcc_h49_ = source34_.opcode
            d_351___mcc_h50_ = source34_.minCapacity
            d_352___mcc_h51_ = source34_.minOperands
            d_353___mcc_h52_ = source34_.pushes
            d_354___mcc_h53_ = source34_.pops
            d_355_pops_ = d_354___mcc_h53_
            d_356_pushes_ = d_353___mcc_h52_
            if (pos_k) == (0):
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Run operator with target 0"))))
            elif True:
                return MiscTypes.Either_Right((pos_k) - (1))
        elif source34_.is_StackOp:
            d_357___mcc_h54_ = source34_.name
            d_358___mcc_h55_ = source34_.opcode
            d_359___mcc_h56_ = source34_.minCapacity
            d_360___mcc_h57_ = source34_.minOperands
            d_361___mcc_h58_ = source34_.pushes
            d_362___mcc_h59_ = source34_.pops
            d_363_opcode_ = d_358___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_363_opcode_)) and ((d_363_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_363_opcode_)) and ((d_363_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_363_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_363_opcode_)) and ((d_363_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_364_k_ = ((d_363_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_364_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_364_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source34_.is_LogOp:
            d_365___mcc_h60_ = source34_.name
            d_366___mcc_h61_ = source34_.opcode
            d_367___mcc_h62_ = source34_.minCapacity
            d_368___mcc_h63_ = source34_.minOperands
            d_369___mcc_h64_ = source34_.pushes
            d_370___mcc_h65_ = source34_.pops
            d_371_pops_ = d_370___mcc_h65_
            d_372_pushes_ = d_369___mcc_h64_
            return MiscTypes.Either_Right((pos_k) + (d_371_pops_))
        elif True:
            d_373___mcc_h66_ = source34_.name
            d_374___mcc_h67_ = source34_.opcode
            d_375___mcc_h68_ = source34_.minCapacity
            d_376___mcc_h69_ = source34_.minOperands
            d_377___mcc_h70_ = source34_.pushes
            d_378___mcc_h71_ = source34_.pops
            d_379_pops_ = d_378___mcc_h71_
            d_380_pushes_ = d_377___mcc_h70_
            if (d_380_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (d_379_pops_))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Sys operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) + (d_379_pops_))

    def NextState(self, s, jumpDests, exit):
        source35_ = (self).op
        if source35_.is_ArithOp:
            d_381___mcc_h0_ = source35_.name
            d_382___mcc_h1_ = source35_.opcode
            d_383___mcc_h2_ = source35_.minCapacity
            d_384___mcc_h3_ = source35_.minOperands
            d_385___mcc_h4_ = source35_.pushes
            d_386___mcc_h5_ = source35_.pops
            d_387_pops_ = d_386___mcc_h5_
            d_388_pushes_ = d_385___mcc_h4_
            if ((s).Size()) >= (d_387_pops_):
                return (((s).PopN(d_387_pops_)).PushNRandom(d_388_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_CompOp:
            d_389___mcc_h6_ = source35_.name
            d_390___mcc_h7_ = source35_.opcode
            d_391___mcc_h8_ = source35_.minCapacity
            d_392___mcc_h9_ = source35_.minOperands
            d_393___mcc_h10_ = source35_.pushes
            d_394___mcc_h11_ = source35_.pops
            d_395_pops_ = d_394___mcc_h11_
            d_396_pushes_ = d_393___mcc_h10_
            if ((s).Size()) >= (d_395_pops_):
                return (((s).PopN(d_395_pops_)).PushNRandom(d_396_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_BitwiseOp:
            d_397___mcc_h12_ = source35_.name
            d_398___mcc_h13_ = source35_.opcode
            d_399___mcc_h14_ = source35_.minCapacity
            d_400___mcc_h15_ = source35_.minOperands
            d_401___mcc_h16_ = source35_.pushes
            d_402___mcc_h17_ = source35_.pops
            d_403_pops_ = d_402___mcc_h17_
            d_404_pushes_ = d_401___mcc_h16_
            if ((s).Size()) >= (d_403_pops_):
                return (((s).PopN(d_403_pops_)).PushNRandom(d_404_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_KeccakOp:
            d_405___mcc_h18_ = source35_.name
            d_406___mcc_h19_ = source35_.opcode
            d_407___mcc_h20_ = source35_.minCapacity
            d_408___mcc_h21_ = source35_.minOperands
            d_409___mcc_h22_ = source35_.pushes
            d_410___mcc_h23_ = source35_.pops
            d_411_pops_ = d_410___mcc_h23_
            d_412_pushes_ = d_409___mcc_h22_
            if ((s).Size()) >= (2):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_EnvOp:
            d_413___mcc_h24_ = source35_.name
            d_414___mcc_h25_ = source35_.opcode
            d_415___mcc_h26_ = source35_.minCapacity
            d_416___mcc_h27_ = source35_.minOperands
            d_417___mcc_h28_ = source35_.pushes
            d_418___mcc_h29_ = source35_.pops
            d_419_pops_ = d_418___mcc_h29_
            d_420_pushes_ = d_417___mcc_h28_
            if ((s).Size()) >= (d_419_pops_):
                return (((s).PopN(d_419_pops_)).PushNRandom(d_420_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        elif source35_.is_MemOp:
            d_421___mcc_h30_ = source35_.name
            d_422___mcc_h31_ = source35_.opcode
            d_423___mcc_h32_ = source35_.minCapacity
            d_424___mcc_h33_ = source35_.minOperands
            d_425___mcc_h34_ = source35_.pushes
            d_426___mcc_h35_ = source35_.pops
            d_427_pops_ = d_426___mcc_h35_
            d_428_pushes_ = d_425___mcc_h34_
            if ((s).Size()) >= (d_427_pops_):
                return (((s).PopN(d_427_pops_)).PushNRandom(d_428_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        elif source35_.is_StorageOp:
            d_429___mcc_h36_ = source35_.name
            d_430___mcc_h37_ = source35_.opcode
            d_431___mcc_h38_ = source35_.minCapacity
            d_432___mcc_h39_ = source35_.minOperands
            d_433___mcc_h40_ = source35_.pushes
            d_434___mcc_h41_ = source35_.pops
            d_435_pops_ = d_434___mcc_h41_
            d_436_pushes_ = d_433___mcc_h40_
            if ((s).Size()) >= (d_435_pops_):
                return (((s).PopN(d_435_pops_)).PushNRandom(d_436_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        elif source35_.is_JumpOp:
            d_437___mcc_h42_ = source35_.name
            d_438___mcc_h43_ = source35_.opcode
            d_439___mcc_h44_ = source35_.minCapacity
            d_440___mcc_h45_ = source35_.minOperands
            d_441___mcc_h46_ = source35_.pushes
            d_442___mcc_h47_ = source35_.pops
            d_443_pops_ = d_442___mcc_h47_
            d_444_pushes_ = d_441___mcc_h46_
            d_445_opcode_ = d_438___mcc_h43_
            if (d_445_opcode_) == (EVMConstants.default__.JUMPDEST):
                return (s).Skip(1)
            elif (d_445_opcode_) == (EVMConstants.default__.JUMP):
                if ((s).Size()) >= (1):
                    source36_ = (s).Peek(0)
                    if source36_.is_Value:
                        d_446___mcc_h72_ = source36_.v
                        d_447_v_ = d_446___mcc_h72_
                        return ((s).Pop()).Goto(d_447_v_)
                    elif True:
                        d_448___mcc_h73_ = source36_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() unknown PC error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_445_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source37_ = (s).Peek(0)
                    if source37_.is_Value:
                        d_449___mcc_h74_ = source37_.v
                        d_450_v_ = d_449___mcc_h74_
                        if (exit) >= (1):
                            return ((s).PopN(2)).Goto(d_450_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_451___mcc_h75_ = source37_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source35_.is_RunOp:
            d_452___mcc_h48_ = source35_.name
            d_453___mcc_h49_ = source35_.opcode
            d_454___mcc_h50_ = source35_.minCapacity
            d_455___mcc_h51_ = source35_.minOperands
            d_456___mcc_h52_ = source35_.pushes
            d_457___mcc_h53_ = source35_.pops
            d_458_pops_ = d_457___mcc_h53_
            d_459_pushes_ = d_456___mcc_h52_
            return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
        elif source35_.is_StackOp:
            d_460___mcc_h54_ = source35_.name
            d_461___mcc_h55_ = source35_.opcode
            d_462___mcc_h56_ = source35_.minCapacity
            d_463___mcc_h57_ = source35_.minOperands
            d_464___mcc_h58_ = source35_.pushes
            d_465___mcc_h59_ = source35_.pops
            d_466_pops_ = d_465___mcc_h59_
            d_467_pushes_ = d_464___mcc_h58_
            d_468_opcode_ = d_461___mcc_h55_
            if ((d_468_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1)):
                return ((s).Pop()).Skip(1)
            elif ((EVMConstants.default__.PUSH0) <= (d_468_opcode_)) and ((d_468_opcode_) <= (EVMConstants.default__.PUSH32)):
                d_469_valToPush_ = (StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)) if (default__.GetArgValuePush((self).arg)) in (jumpDests) else StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))
                return ((s).Push(d_469_valToPush_)).Skip((1) + ((d_468_opcode_) - (EVMConstants.default__.PUSH0)))
            elif (((EVMConstants.default__.DUP1) <= (d_468_opcode_)) and ((d_468_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_468_opcode_) - (EVMConstants.default__.DUP1)) + (1))):
                return ((s).Dup(((d_468_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif (((EVMConstants.default__.SWAP1) <= (d_468_opcode_)) and ((d_468_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_468_opcode_) - (EVMConstants.default__.SWAP1)) + (1))):
                return ((s).Swap(((d_468_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        elif source35_.is_LogOp:
            d_470___mcc_h60_ = source35_.name
            d_471___mcc_h61_ = source35_.opcode
            d_472___mcc_h62_ = source35_.minCapacity
            d_473___mcc_h63_ = source35_.minOperands
            d_474___mcc_h64_ = source35_.pushes
            d_475___mcc_h65_ = source35_.pops
            d_476_pops_ = d_475___mcc_h65_
            d_477_pushes_ = d_474___mcc_h64_
            if ((s).Size()) >= (d_476_pops_):
                return ((s).PopN(d_476_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        elif True:
            d_478___mcc_h66_ = source35_.name
            d_479___mcc_h67_ = source35_.opcode
            d_480___mcc_h68_ = source35_.minCapacity
            d_481___mcc_h69_ = source35_.minOperands
            d_482___mcc_h70_ = source35_.pushes
            d_483___mcc_h71_ = source35_.pops
            d_484_pops_ = d_483___mcc_h71_
            d_485_pushes_ = d_482___mcc_h70_
            d_486_op_ = d_479___mcc_h67_
            if (((d_486_op_) == (EVMConstants.default__.INVALID)) or ((d_486_op_) == (EVMConstants.default__.STOP))) or ((d_486_op_) == (EVMConstants.default__.REVERT)):
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))
            elif ((s).Size()) >= (d_484_pops_):
                return (((s).PopN(d_484_pops_)).PushNRandom(d_485_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source38_ = (self).op
        if source38_.is_ArithOp:
            d_487___mcc_h0_ = source38_.name
            d_488___mcc_h1_ = source38_.opcode
            d_489___mcc_h2_ = source38_.minCapacity
            d_490___mcc_h3_ = source38_.minOperands
            d_491___mcc_h4_ = source38_.pushes
            d_492___mcc_h5_ = source38_.pops
            d_493_pops_ = d_492___mcc_h5_
            d_494_pushes_ = d_491___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda6_(d_496_pos_):
                    return (d_496_pos_) + (1)

                d_495_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_)
                return WeakPre.Cond_StCond(d_495_shiftByOne_, (c).TrackedVals())
        elif source38_.is_CompOp:
            d_497___mcc_h6_ = source38_.name
            d_498___mcc_h7_ = source38_.opcode
            d_499___mcc_h8_ = source38_.minCapacity
            d_500___mcc_h9_ = source38_.minOperands
            d_501___mcc_h10_ = source38_.pushes
            d_502___mcc_h11_ = source38_.pops
            d_503_pops_ = d_502___mcc_h11_
            d_504_pushes_ = d_501___mcc_h10_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda7_(d_506_pops_, d_507_pushes_):
                    def lambda8_(d_508_pos_):
                        return ((d_508_pos_) + (d_506_pops_)) - (d_507_pushes_)

                    return lambda8_

                d_505_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda7_(d_503_pops_, d_504_pushes_))
                return WeakPre.Cond_StCond(d_505_shiftBy_, (c).TrackedVals())
        elif source38_.is_BitwiseOp:
            d_509___mcc_h12_ = source38_.name
            d_510___mcc_h13_ = source38_.opcode
            d_511___mcc_h14_ = source38_.minCapacity
            d_512___mcc_h15_ = source38_.minOperands
            d_513___mcc_h16_ = source38_.pushes
            d_514___mcc_h17_ = source38_.pops
            d_515_pops_ = d_514___mcc_h17_
            d_516_pushes_ = d_513___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda9_(d_518_pops_, d_519_pushes_):
                    def lambda10_(d_520_pos_):
                        return ((d_520_pos_) + (d_518_pops_)) - (d_519_pushes_)

                    return lambda10_

                d_517_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda9_(d_515_pops_, d_516_pushes_))
                return WeakPre.Cond_StCond(d_517_shiftBy_, (c).TrackedVals())
        elif source38_.is_KeccakOp:
            d_521___mcc_h18_ = source38_.name
            d_522___mcc_h19_ = source38_.opcode
            d_523___mcc_h20_ = source38_.minCapacity
            d_524___mcc_h21_ = source38_.minOperands
            d_525___mcc_h22_ = source38_.pushes
            d_526___mcc_h23_ = source38_.pops
            d_527_pops_ = d_526___mcc_h23_
            d_528_pushes_ = d_525___mcc_h22_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda11_(d_530_pos_):
                    return (d_530_pos_) + (1)

                d_529_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda11_)
                return WeakPre.Cond_StCond(d_529_shiftByOne_, (c).TrackedVals())
        elif source38_.is_EnvOp:
            d_531___mcc_h24_ = source38_.name
            d_532___mcc_h25_ = source38_.opcode
            d_533___mcc_h26_ = source38_.minCapacity
            d_534___mcc_h27_ = source38_.minOperands
            d_535___mcc_h28_ = source38_.pushes
            d_536___mcc_h29_ = source38_.pops
            d_537_pops_ = d_536___mcc_h29_
            d_538_pushes_ = d_535___mcc_h28_
            if ((d_538_pushes_) == (1)) and ((d_537_pops_) == (0)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda12_(d_540_pos_):
                        return (d_540_pos_) - (1)

                    d_539_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda12_)
                    return WeakPre.Cond_StCond(d_539_shiftByOne_, (c).TrackedVals())
            elif ((d_538_pushes_) == (1)) and ((d_537_pops_) == (1)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
            elif True:
                def lambda13_(d_542_pops_, d_543_pushes_):
                    def lambda14_(d_544_pos_):
                        return ((d_544_pos_) + (d_542_pops_)) - (d_543_pushes_)

                    return lambda14_

                d_541_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda13_(d_537_pops_, d_538_pushes_))
                return WeakPre.Cond_StCond(d_541_shiftBy_, (c).TrackedVals())
        elif source38_.is_MemOp:
            d_545___mcc_h30_ = source38_.name
            d_546___mcc_h31_ = source38_.opcode
            d_547___mcc_h32_ = source38_.minCapacity
            d_548___mcc_h33_ = source38_.minOperands
            d_549___mcc_h34_ = source38_.pushes
            d_550___mcc_h35_ = source38_.pops
            d_551_pops_ = d_550___mcc_h35_
            d_552_pushes_ = d_549___mcc_h34_
            if (d_552_pushes_) == (0):
                def lambda15_(d_554_pos_):
                    return (d_554_pos_) + (2)

                d_553_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda15_)
                return WeakPre.Cond_StCond(d_553_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source38_.is_StorageOp:
            d_555___mcc_h36_ = source38_.name
            d_556___mcc_h37_ = source38_.opcode
            d_557___mcc_h38_ = source38_.minCapacity
            d_558___mcc_h39_ = source38_.minOperands
            d_559___mcc_h40_ = source38_.pushes
            d_560___mcc_h41_ = source38_.pops
            d_561_pops_ = d_560___mcc_h41_
            d_562_pushes_ = d_559___mcc_h40_
            if (d_562_pushes_) == (0):
                def lambda16_(d_564_pos_):
                    return (d_564_pos_) + (2)

                d_563_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                return WeakPre.Cond_StCond(d_563_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source38_.is_JumpOp:
            d_565___mcc_h42_ = source38_.name
            d_566___mcc_h43_ = source38_.opcode
            d_567___mcc_h44_ = source38_.minCapacity
            d_568___mcc_h45_ = source38_.minOperands
            d_569___mcc_h46_ = source38_.pushes
            d_570___mcc_h47_ = source38_.pops
            d_571_opcode_ = d_566___mcc_h43_
            if (d_571_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_571_opcode_)) and ((d_571_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_572_k_ = ((d_571_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda17_(d_574_k_):
                    def lambda18_(d_575_pos_):
                        return (d_575_pos_) + (d_574_k_)

                    return lambda18_

                d_573_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda17_(d_572_k_))
                return WeakPre.Cond_StCond(d_573_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source38_.is_RunOp:
            d_576___mcc_h48_ = source38_.name
            d_577___mcc_h49_ = source38_.opcode
            d_578___mcc_h50_ = source38_.minCapacity
            d_579___mcc_h51_ = source38_.minOperands
            d_580___mcc_h52_ = source38_.pushes
            d_581___mcc_h53_ = source38_.pops
            d_582_opcode_ = d_577___mcc_h49_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda19_(d_584_pos_):
                    return (d_584_pos_) - (1)

                d_583_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda19_)
                return WeakPre.Cond_StCond(d_583_shiftByOne_, (c).TrackedVals())
        elif source38_.is_StackOp:
            d_585___mcc_h54_ = source38_.name
            d_586___mcc_h55_ = source38_.opcode
            d_587___mcc_h56_ = source38_.minCapacity
            d_588___mcc_h57_ = source38_.minOperands
            d_589___mcc_h58_ = source38_.pushes
            d_590___mcc_h59_ = source38_.pops
            d_591_opcode_ = d_586___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_591_opcode_)) and ((d_591_opcode_) <= (EVMConstants.default__.PUSH32)):
                source39_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source39_.is_None:
                    def lambda20_(d_593_pos_):
                        return (d_593_pos_) - (1)

                    d_592_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda20_)
                    return WeakPre.Cond_StCond(d_592_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_594___mcc_h72_ = source39_.v
                    d_595_i_ = d_594___mcc_h72_
                    d_596_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_597___v142_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_595_i_)) == ((d_596_argVal_).Extract()):
                        d_598_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_595_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_595_i_) + (1)::]))
                        if (len(d_598_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda21_(d_600_pos_):
                                return (d_600_pos_) - (1)

                            d_599_shiftByMinusOne_ = MiscTypes.default__.Map(d_598_filtered_, lambda21_)
                            return WeakPre.Cond_StCond(d_599_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_595_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_595_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_591_opcode_)) and ((d_591_opcode_) <= (EVMConstants.default__.DUP16)):
                source40_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source40_.is_None:
                    def lambda22_(d_602_pos_):
                        return (d_602_pos_) - (1)

                    d_601_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda22_)
                    return WeakPre.Cond_StCond(d_601_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_603___mcc_h73_ = source40_.v
                    d_604_index0_ = d_603___mcc_h73_
                    source41_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_591_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source41_.is_None:
                        def lambda23_(d_606_opcode_):
                            def lambda24_(d_607_pos_):
                                return ((d_606_opcode_) - (EVMConstants.default__.DUP1) if (d_607_pos_) == (0) else (d_607_pos_) - (1))

                            return lambda24_

                        d_605_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda23_(d_591_opcode_))
                        return WeakPre.Cond_StCond(d_605_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_608___mcc_h74_ = source41_.v
                        d_609_index_ = d_608___mcc_h74_
                        if ((c).TrackedValAt(d_604_index0_)) == ((c).TrackedValAt(d_609_index_)):
                            d_610_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_604_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_604_index0_) + (1)::]))
                            def lambda25_(d_612_pos_):
                                return (d_612_pos_) - (1)

                            d_611_shiftByMinusOne_ = MiscTypes.default__.Map(d_610_filtered_, lambda25_)
                            return WeakPre.Cond_StCond(d_611_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_604_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_604_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_591_opcode_)) and ((d_591_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_613_k_ = ((d_591_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda26_(d_615_k_):
                    def lambda27_(d_616_pos_):
                        return (d_615_k_ if (d_616_pos_) == (0) else (0 if (d_616_pos_) == (d_615_k_) else d_616_pos_))

                    return lambda27_

                d_614_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda26_(d_613_k_))
                return WeakPre.Cond_StCond(d_614_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda28_(d_618_i_):
                    return (d_618_i_) + (1)

                d_617_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda28_)
                return WeakPre.Cond_StCond(d_617_shiftByOne_, (c).TrackedVals())
        elif source38_.is_LogOp:
            d_619___mcc_h60_ = source38_.name
            d_620___mcc_h61_ = source38_.opcode
            d_621___mcc_h62_ = source38_.minCapacity
            d_622___mcc_h63_ = source38_.minOperands
            d_623___mcc_h64_ = source38_.pushes
            d_624___mcc_h65_ = source38_.pops
            d_625_pops_ = d_624___mcc_h65_
            d_626_pushes_ = d_623___mcc_h64_
            d_627_opcode_ = d_620___mcc_h61_
            def lambda29_(d_629_pops_):
                def lambda30_(d_630_pos_):
                    return (d_630_pos_) + (d_629_pops_)

                return lambda30_

            d_628_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda29_(d_625_pops_))
            return WeakPre.Cond_StCond(d_628_shiftBy_, (c).TrackedVals())
        elif True:
            d_631___mcc_h66_ = source38_.name
            d_632___mcc_h67_ = source38_.opcode
            d_633___mcc_h68_ = source38_.minCapacity
            d_634___mcc_h69_ = source38_.minOperands
            d_635___mcc_h70_ = source38_.pushes
            d_636___mcc_h71_ = source38_.pops
            d_637_pops_ = d_636___mcc_h71_
            d_638_pushes_ = d_635___mcc_h70_
            d_639_opcode_ = d_632___mcc_h67_
            if (d_638_pushes_) == (0):
                def lambda31_(d_641_pops_):
                    def lambda32_(d_642_pos_):
                        return (d_642_pos_) + (d_641_pops_)

                    return lambda32_

                d_640_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda31_(d_637_pops_))
                return WeakPre.Cond_StCond(d_640_shiftBy_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda33_(d_644_pops_):
                        def lambda34_(d_645_pos_):
                            return (d_645_pos_) + (d_644_pops_)

                        return lambda34_

                    d_643_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda33_(d_637_pops_))
                    return WeakPre.Cond_StCond(d_643_shiftBy_, (c).TrackedVals())


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

