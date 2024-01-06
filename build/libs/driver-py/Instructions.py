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
        d_196_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_197___v149_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_196_pad_) + (xc))).Extract()

    @staticmethod
    def ToDot(xi):
        d_198___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_198___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_198___accumulator_ = (d_198___accumulator_) + (((xi)[0]).ToHTML())
                    in32_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in32_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Colours(i):
        source33_ = (i).op
        if source33_.is_ArithOp:
            d_199___mcc_h0_ = source33_.name
            d_200___mcc_h1_ = source33_.opcode
            d_201___mcc_h2_ = source33_.minCapacity
            d_202___mcc_h3_ = source33_.minOperands
            d_203___mcc_h4_ = source33_.pushes
            d_204___mcc_h5_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#316152")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#c6eb76")))
        elif source33_.is_CompOp:
            d_205___mcc_h6_ = source33_.name
            d_206___mcc_h7_ = source33_.opcode
            d_207___mcc_h8_ = source33_.minCapacity
            d_208___mcc_h9_ = source33_.minOperands
            d_209___mcc_h10_ = source33_.pushes
            d_210___mcc_h11_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkgoldenrod")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "bisque")))
        elif source33_.is_BitwiseOp:
            d_211___mcc_h12_ = source33_.name
            d_212___mcc_h13_ = source33_.opcode
            d_213___mcc_h14_ = source33_.minCapacity
            d_214___mcc_h15_ = source33_.minOperands
            d_215___mcc_h16_ = source33_.pushes
            d_216___mcc_h17_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "orange")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#f3f383")))
        elif source33_.is_KeccakOp:
            d_217___mcc_h18_ = source33_.name
            d_218___mcc_h19_ = source33_.opcode
            d_219___mcc_h20_ = source33_.minCapacity
            d_220___mcc_h21_ = source33_.minOperands
            d_221___mcc_h22_ = source33_.pushes
            d_222___mcc_h23_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "grey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "linen")))
        elif source33_.is_EnvOp:
            d_223___mcc_h24_ = source33_.name
            d_224___mcc_h25_ = source33_.opcode
            d_225___mcc_h26_ = source33_.minCapacity
            d_226___mcc_h27_ = source33_.minOperands
            d_227___mcc_h28_ = source33_.pushes
            d_228___mcc_h29_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkslategrey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightgrey")))
        elif source33_.is_MemOp:
            d_229___mcc_h30_ = source33_.name
            d_230___mcc_h31_ = source33_.opcode
            d_231___mcc_h32_ = source33_.minCapacity
            d_232___mcc_h33_ = source33_.minOperands
            d_233___mcc_h34_ = source33_.pushes
            d_234___mcc_h35_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "wheat")))
        elif source33_.is_StorageOp:
            d_235___mcc_h36_ = source33_.name
            d_236___mcc_h37_ = source33_.opcode
            d_237___mcc_h38_ = source33_.minCapacity
            d_238___mcc_h39_ = source33_.minOperands
            d_239___mcc_h40_ = source33_.pushes
            d_240___mcc_h41_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "fuchsia")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "mistyrose")))
        elif source33_.is_JumpOp:
            d_241___mcc_h42_ = source33_.name
            d_242___mcc_h43_ = source33_.opcode
            d_243___mcc_h44_ = source33_.minCapacity
            d_244___mcc_h45_ = source33_.minOperands
            d_245___mcc_h46_ = source33_.pushes
            d_246___mcc_h47_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "purple")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "thistle")))
        elif source33_.is_RunOp:
            d_247___mcc_h48_ = source33_.name
            d_248___mcc_h49_ = source33_.opcode
            d_249___mcc_h50_ = source33_.minCapacity
            d_250___mcc_h51_ = source33_.minOperands
            d_251___mcc_h52_ = source33_.pushes
            d_252___mcc_h53_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tan")))
        elif source33_.is_StackOp:
            d_253___mcc_h54_ = source33_.name
            d_254___mcc_h55_ = source33_.opcode
            d_255___mcc_h56_ = source33_.minCapacity
            d_256___mcc_h57_ = source33_.minOperands
            d_257___mcc_h58_ = source33_.pushes
            d_258___mcc_h59_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "royalblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "powderblue")))
        elif source33_.is_LogOp:
            d_259___mcc_h60_ = source33_.name
            d_260___mcc_h61_ = source33_.opcode
            d_261___mcc_h62_ = source33_.minCapacity
            d_262___mcc_h63_ = source33_.minOperands
            d_263___mcc_h64_ = source33_.pushes
            d_264___mcc_h65_ = source33_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "cornflowerblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lavender")))
        elif True:
            d_265___mcc_h66_ = source33_.name
            d_266___mcc_h67_ = source33_.opcode
            d_267___mcc_h68_ = source33_.minCapacity
            d_268___mcc_h69_ = source33_.minOperands
            d_269___mcc_h70_ = source33_.pushes
            d_270___mcc_h71_ = source33_.pops
            d_271_opcode_ = d_266___mcc_h67_
            if ((d_271_opcode_) == (EVMConstants.default__.STOP)) or ((d_271_opcode_) == (EVMConstants.default__.REVERT)):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "brown")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightsalmon")))
            elif (d_271_opcode_) == (EVMConstants.default__.RETURN):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "teal")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "greenyellow")))
            elif ((((d_271_opcode_) == (EVMConstants.default__.CALL)) or ((d_271_opcode_) == (EVMConstants.default__.CALLCODE))) or ((d_271_opcode_) == (EVMConstants.default__.DELEGATECALL))) or ((d_271_opcode_) == (EVMConstants.default__.STATICCALL)):
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
        d_272_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_272_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_272_x_) if (len(d_272_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def Equiv(self, i):
        return (((self).op) == ((i).op)) and (((self).arg) == ((i).arg))

    def ToHTML(self):
        d_273_x_ = (self).arg
        d_274_cols_ = default__.Colours(self)
        d_275_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_276___v0_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_277_insText_ = (((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_274_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_273_x_) if (((self).op).opcode) == (EVMConstants.default__.INVALID) else (((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_274_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_273_x_) if (len(d_273_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))))
        return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (d_275_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":")))) + (d_277_insText_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))

    def ToHTMLTable(self, entryPortTag, exitPortTag):
        d_278_cols_ = default__.Colours(self)
        d_279_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_280___v1_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_281_gasLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981;"))
        d_282_oplineTD_ = ((((((((((((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" "))) + (entryPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x")))) + (d_279_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " </TD>\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: ")))) + (EVMToolTips.default__.Gas(((self).op).opcode))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " \" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "target=\"_blank\" href=\"")))) + (EVMToolTips.default__.gasRefLine)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (d_281_gasLine_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")))) + ((d_278_cols_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" align=\"left\" cellpadding=\"3\" ")))) + (exitPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"")))) + (EVMToolTips.default__.bytecodeRefLine)) + (Int.default__.NatToString((EVMToolTips.default__.ToolTip(((self).op).opcode))[1]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" target=\"_blank\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " tooltip=\"")))) + ((EVMToolTips.default__.ToolTip(((self).op).opcode))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\"")))) + ((d_278_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))
        d_283_arglineTD_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" align=\"left\">"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  0x")))) + ((self).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>"))) if (len((self).arg)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_284_lineTR_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR>"))) + (d_282_oplineTD_)) + (d_283_arglineTD_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR>")))
        d_285_itemTable_ = ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE  border=\"0\" cellpadding=\"0\" cellborder=\"0\" CELLSPACING=\"1\">"))) + (d_284_lineTR_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>")))
        return d_285_itemTable_

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
            d_286___mcc_h0_ = source34_.name
            d_287___mcc_h1_ = source34_.opcode
            d_288___mcc_h2_ = source34_.minCapacity
            d_289___mcc_h3_ = source34_.minOperands
            d_290___mcc_h4_ = source34_.pushes
            d_291___mcc_h5_ = source34_.pops
            d_292_pops_ = d_291___mcc_h5_
            d_293_pushes_ = d_290___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source34_.is_CompOp:
            d_294___mcc_h6_ = source34_.name
            d_295___mcc_h7_ = source34_.opcode
            d_296___mcc_h8_ = source34_.minCapacity
            d_297___mcc_h9_ = source34_.minOperands
            d_298___mcc_h10_ = source34_.pushes
            d_299___mcc_h11_ = source34_.pops
            d_300_pops_ = d_299___mcc_h11_
            d_301_pushes_ = d_298___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_300_pops_)) - (d_301_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source34_.is_BitwiseOp:
            d_302___mcc_h12_ = source34_.name
            d_303___mcc_h13_ = source34_.opcode
            d_304___mcc_h14_ = source34_.minCapacity
            d_305___mcc_h15_ = source34_.minOperands
            d_306___mcc_h16_ = source34_.pushes
            d_307___mcc_h17_ = source34_.pops
            d_308_pops_ = d_307___mcc_h17_
            d_309_pushes_ = d_306___mcc_h16_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_308_pops_)) - (d_309_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Bitwise operator with target 0"))))
        elif source34_.is_KeccakOp:
            d_310___mcc_h18_ = source34_.name
            d_311___mcc_h19_ = source34_.opcode
            d_312___mcc_h20_ = source34_.minCapacity
            d_313___mcc_h21_ = source34_.minOperands
            d_314___mcc_h22_ = source34_.pushes
            d_315___mcc_h23_ = source34_.pops
            d_316_pops_ = d_315___mcc_h23_
            d_317_pushes_ = d_314___mcc_h22_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Keccak operator with target 0"))))
        elif source34_.is_EnvOp:
            d_318___mcc_h24_ = source34_.name
            d_319___mcc_h25_ = source34_.opcode
            d_320___mcc_h26_ = source34_.minCapacity
            d_321___mcc_h27_ = source34_.minOperands
            d_322___mcc_h28_ = source34_.pushes
            d_323___mcc_h29_ = source34_.pops
            d_324_pops_ = d_323___mcc_h29_
            d_325_pushes_ = d_322___mcc_h28_
            if ((d_325_pushes_) == (1)) and ((d_324_pops_) == (0)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((d_325_pushes_) == (1)) and ((d_324_pops_) == (1)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
            elif True:
                return MiscTypes.Either_Right(((pos_k) + (d_324_pops_)) - (d_325_pushes_))
        elif source34_.is_MemOp:
            d_326___mcc_h30_ = source34_.name
            d_327___mcc_h31_ = source34_.opcode
            d_328___mcc_h32_ = source34_.minCapacity
            d_329___mcc_h33_ = source34_.minOperands
            d_330___mcc_h34_ = source34_.pushes
            d_331___mcc_h35_ = source34_.pops
            d_332_pops_ = d_331___mcc_h35_
            d_333_pushes_ = d_330___mcc_h34_
            if (d_333_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Mem operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source34_.is_StorageOp:
            d_334___mcc_h36_ = source34_.name
            d_335___mcc_h37_ = source34_.opcode
            d_336___mcc_h38_ = source34_.minCapacity
            d_337___mcc_h39_ = source34_.minOperands
            d_338___mcc_h40_ = source34_.pushes
            d_339___mcc_h41_ = source34_.pops
            d_340_pops_ = d_339___mcc_h41_
            d_341_pushes_ = d_338___mcc_h40_
            if (d_341_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Storage operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source34_.is_JumpOp:
            d_342___mcc_h42_ = source34_.name
            d_343___mcc_h43_ = source34_.opcode
            d_344___mcc_h44_ = source34_.minCapacity
            d_345___mcc_h45_ = source34_.minOperands
            d_346___mcc_h46_ = source34_.pushes
            d_347___mcc_h47_ = source34_.pops
            d_348_opcode_ = d_343___mcc_h43_
            if (d_348_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_348_opcode_)) and ((d_348_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_349_k_ = ((d_348_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_349_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source34_.is_RunOp:
            d_350___mcc_h48_ = source34_.name
            d_351___mcc_h49_ = source34_.opcode
            d_352___mcc_h50_ = source34_.minCapacity
            d_353___mcc_h51_ = source34_.minOperands
            d_354___mcc_h52_ = source34_.pushes
            d_355___mcc_h53_ = source34_.pops
            d_356_pops_ = d_355___mcc_h53_
            d_357_pushes_ = d_354___mcc_h52_
            if (pos_k) == (0):
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Run operator with target 0"))))
            elif True:
                return MiscTypes.Either_Right((pos_k) - (1))
        elif source34_.is_StackOp:
            d_358___mcc_h54_ = source34_.name
            d_359___mcc_h55_ = source34_.opcode
            d_360___mcc_h56_ = source34_.minCapacity
            d_361___mcc_h57_ = source34_.minOperands
            d_362___mcc_h58_ = source34_.pushes
            d_363___mcc_h59_ = source34_.pops
            d_364_opcode_ = d_359___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_364_opcode_)) and ((d_364_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_364_opcode_)) and ((d_364_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_364_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_364_opcode_)) and ((d_364_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_365_k_ = ((d_364_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_365_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_365_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source34_.is_LogOp:
            d_366___mcc_h60_ = source34_.name
            d_367___mcc_h61_ = source34_.opcode
            d_368___mcc_h62_ = source34_.minCapacity
            d_369___mcc_h63_ = source34_.minOperands
            d_370___mcc_h64_ = source34_.pushes
            d_371___mcc_h65_ = source34_.pops
            d_372_pops_ = d_371___mcc_h65_
            d_373_pushes_ = d_370___mcc_h64_
            return MiscTypes.Either_Right((pos_k) + (d_372_pops_))
        elif True:
            d_374___mcc_h66_ = source34_.name
            d_375___mcc_h67_ = source34_.opcode
            d_376___mcc_h68_ = source34_.minCapacity
            d_377___mcc_h69_ = source34_.minOperands
            d_378___mcc_h70_ = source34_.pushes
            d_379___mcc_h71_ = source34_.pops
            d_380_pops_ = d_379___mcc_h71_
            d_381_pushes_ = d_378___mcc_h70_
            if (d_381_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (d_380_pops_))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Sys operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) + (d_380_pops_))

    def NextState(self, s, jumpDests, exit):
        source35_ = (self).op
        if source35_.is_ArithOp:
            d_382___mcc_h0_ = source35_.name
            d_383___mcc_h1_ = source35_.opcode
            d_384___mcc_h2_ = source35_.minCapacity
            d_385___mcc_h3_ = source35_.minOperands
            d_386___mcc_h4_ = source35_.pushes
            d_387___mcc_h5_ = source35_.pops
            d_388_pops_ = d_387___mcc_h5_
            d_389_pushes_ = d_386___mcc_h4_
            if ((s).Size()) >= (d_388_pops_):
                return (((s).PopN(d_388_pops_)).PushNRandom(d_389_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_CompOp:
            d_390___mcc_h6_ = source35_.name
            d_391___mcc_h7_ = source35_.opcode
            d_392___mcc_h8_ = source35_.minCapacity
            d_393___mcc_h9_ = source35_.minOperands
            d_394___mcc_h10_ = source35_.pushes
            d_395___mcc_h11_ = source35_.pops
            d_396_pops_ = d_395___mcc_h11_
            d_397_pushes_ = d_394___mcc_h10_
            if ((s).Size()) >= (d_396_pops_):
                return (((s).PopN(d_396_pops_)).PushNRandom(d_397_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_BitwiseOp:
            d_398___mcc_h12_ = source35_.name
            d_399___mcc_h13_ = source35_.opcode
            d_400___mcc_h14_ = source35_.minCapacity
            d_401___mcc_h15_ = source35_.minOperands
            d_402___mcc_h16_ = source35_.pushes
            d_403___mcc_h17_ = source35_.pops
            d_404_pops_ = d_403___mcc_h17_
            d_405_pushes_ = d_402___mcc_h16_
            if ((s).Size()) >= (d_404_pops_):
                return (((s).PopN(d_404_pops_)).PushNRandom(d_405_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_KeccakOp:
            d_406___mcc_h18_ = source35_.name
            d_407___mcc_h19_ = source35_.opcode
            d_408___mcc_h20_ = source35_.minCapacity
            d_409___mcc_h21_ = source35_.minOperands
            d_410___mcc_h22_ = source35_.pushes
            d_411___mcc_h23_ = source35_.pops
            d_412_pops_ = d_411___mcc_h23_
            d_413_pushes_ = d_410___mcc_h22_
            if ((s).Size()) >= (2):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source35_.is_EnvOp:
            d_414___mcc_h24_ = source35_.name
            d_415___mcc_h25_ = source35_.opcode
            d_416___mcc_h26_ = source35_.minCapacity
            d_417___mcc_h27_ = source35_.minOperands
            d_418___mcc_h28_ = source35_.pushes
            d_419___mcc_h29_ = source35_.pops
            d_420_pops_ = d_419___mcc_h29_
            d_421_pushes_ = d_418___mcc_h28_
            if ((s).Size()) >= (d_420_pops_):
                return (((s).PopN(d_420_pops_)).PushNRandom(d_421_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        elif source35_.is_MemOp:
            d_422___mcc_h30_ = source35_.name
            d_423___mcc_h31_ = source35_.opcode
            d_424___mcc_h32_ = source35_.minCapacity
            d_425___mcc_h33_ = source35_.minOperands
            d_426___mcc_h34_ = source35_.pushes
            d_427___mcc_h35_ = source35_.pops
            d_428_pops_ = d_427___mcc_h35_
            d_429_pushes_ = d_426___mcc_h34_
            if ((s).Size()) >= (d_428_pops_):
                return (((s).PopN(d_428_pops_)).PushNRandom(d_429_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        elif source35_.is_StorageOp:
            d_430___mcc_h36_ = source35_.name
            d_431___mcc_h37_ = source35_.opcode
            d_432___mcc_h38_ = source35_.minCapacity
            d_433___mcc_h39_ = source35_.minOperands
            d_434___mcc_h40_ = source35_.pushes
            d_435___mcc_h41_ = source35_.pops
            d_436_pops_ = d_435___mcc_h41_
            d_437_pushes_ = d_434___mcc_h40_
            if ((s).Size()) >= (d_436_pops_):
                return (((s).PopN(d_436_pops_)).PushNRandom(d_437_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        elif source35_.is_JumpOp:
            d_438___mcc_h42_ = source35_.name
            d_439___mcc_h43_ = source35_.opcode
            d_440___mcc_h44_ = source35_.minCapacity
            d_441___mcc_h45_ = source35_.minOperands
            d_442___mcc_h46_ = source35_.pushes
            d_443___mcc_h47_ = source35_.pops
            d_444_pops_ = d_443___mcc_h47_
            d_445_pushes_ = d_442___mcc_h46_
            d_446_opcode_ = d_439___mcc_h43_
            if (d_446_opcode_) == (EVMConstants.default__.JUMPDEST):
                return (s).Skip(1)
            elif (d_446_opcode_) == (EVMConstants.default__.JUMP):
                if ((s).Size()) >= (1):
                    source36_ = (s).Peek(0)
                    if source36_.is_Value:
                        d_447___mcc_h72_ = source36_.v
                        d_448_v_ = d_447___mcc_h72_
                        return ((s).Pop()).Goto(d_448_v_)
                    elif True:
                        d_449___mcc_h73_ = source36_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() unknown PC error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_446_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source37_ = (s).Peek(0)
                    if source37_.is_Value:
                        d_450___mcc_h74_ = source37_.v
                        d_451_v_ = d_450___mcc_h74_
                        if (exit) >= (1):
                            return ((s).PopN(2)).Goto(d_451_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_452___mcc_h75_ = source37_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source35_.is_RunOp:
            d_453___mcc_h48_ = source35_.name
            d_454___mcc_h49_ = source35_.opcode
            d_455___mcc_h50_ = source35_.minCapacity
            d_456___mcc_h51_ = source35_.minOperands
            d_457___mcc_h52_ = source35_.pushes
            d_458___mcc_h53_ = source35_.pops
            d_459_pops_ = d_458___mcc_h53_
            d_460_pushes_ = d_457___mcc_h52_
            return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
        elif source35_.is_StackOp:
            d_461___mcc_h54_ = source35_.name
            d_462___mcc_h55_ = source35_.opcode
            d_463___mcc_h56_ = source35_.minCapacity
            d_464___mcc_h57_ = source35_.minOperands
            d_465___mcc_h58_ = source35_.pushes
            d_466___mcc_h59_ = source35_.pops
            d_467_pops_ = d_466___mcc_h59_
            d_468_pushes_ = d_465___mcc_h58_
            d_469_opcode_ = d_462___mcc_h55_
            if ((d_469_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1)):
                return ((s).Pop()).Skip(1)
            elif ((EVMConstants.default__.PUSH0) <= (d_469_opcode_)) and ((d_469_opcode_) <= (EVMConstants.default__.PUSH32)):
                d_470_valToPush_ = (StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)) if (default__.GetArgValuePush((self).arg)) in (jumpDests) else StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))
                return ((s).Push(d_470_valToPush_)).Skip((1) + ((d_469_opcode_) - (EVMConstants.default__.PUSH0)))
            elif (((EVMConstants.default__.DUP1) <= (d_469_opcode_)) and ((d_469_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_469_opcode_) - (EVMConstants.default__.DUP1)) + (1))):
                return ((s).Dup(((d_469_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif (((EVMConstants.default__.SWAP1) <= (d_469_opcode_)) and ((d_469_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_469_opcode_) - (EVMConstants.default__.SWAP1)) + (1))):
                return ((s).Swap(((d_469_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        elif source35_.is_LogOp:
            d_471___mcc_h60_ = source35_.name
            d_472___mcc_h61_ = source35_.opcode
            d_473___mcc_h62_ = source35_.minCapacity
            d_474___mcc_h63_ = source35_.minOperands
            d_475___mcc_h64_ = source35_.pushes
            d_476___mcc_h65_ = source35_.pops
            d_477_pops_ = d_476___mcc_h65_
            d_478_pushes_ = d_475___mcc_h64_
            if ((s).Size()) >= (d_477_pops_):
                return ((s).PopN(d_477_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        elif True:
            d_479___mcc_h66_ = source35_.name
            d_480___mcc_h67_ = source35_.opcode
            d_481___mcc_h68_ = source35_.minCapacity
            d_482___mcc_h69_ = source35_.minOperands
            d_483___mcc_h70_ = source35_.pushes
            d_484___mcc_h71_ = source35_.pops
            d_485_pops_ = d_484___mcc_h71_
            d_486_pushes_ = d_483___mcc_h70_
            d_487_op_ = d_480___mcc_h67_
            if (((d_487_op_) == (EVMConstants.default__.INVALID)) or ((d_487_op_) == (EVMConstants.default__.STOP))) or ((d_487_op_) == (EVMConstants.default__.REVERT)):
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))
            elif ((s).Size()) >= (d_485_pops_):
                return (((s).PopN(d_485_pops_)).PushNRandom(d_486_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source38_ = (self).op
        if source38_.is_ArithOp:
            d_488___mcc_h0_ = source38_.name
            d_489___mcc_h1_ = source38_.opcode
            d_490___mcc_h2_ = source38_.minCapacity
            d_491___mcc_h3_ = source38_.minOperands
            d_492___mcc_h4_ = source38_.pushes
            d_493___mcc_h5_ = source38_.pops
            d_494_pops_ = d_493___mcc_h5_
            d_495_pushes_ = d_492___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda6_(d_497_pos_):
                    return (d_497_pos_) + (1)

                d_496_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_)
                return WeakPre.Cond_StCond(d_496_shiftByOne_, (c).TrackedVals())
        elif source38_.is_CompOp:
            d_498___mcc_h6_ = source38_.name
            d_499___mcc_h7_ = source38_.opcode
            d_500___mcc_h8_ = source38_.minCapacity
            d_501___mcc_h9_ = source38_.minOperands
            d_502___mcc_h10_ = source38_.pushes
            d_503___mcc_h11_ = source38_.pops
            d_504_pops_ = d_503___mcc_h11_
            d_505_pushes_ = d_502___mcc_h10_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda7_(d_507_pops_, d_508_pushes_):
                    def lambda8_(d_509_pos_):
                        return ((d_509_pos_) + (d_507_pops_)) - (d_508_pushes_)

                    return lambda8_

                d_506_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda7_(d_504_pops_, d_505_pushes_))
                return WeakPre.Cond_StCond(d_506_shiftBy_, (c).TrackedVals())
        elif source38_.is_BitwiseOp:
            d_510___mcc_h12_ = source38_.name
            d_511___mcc_h13_ = source38_.opcode
            d_512___mcc_h14_ = source38_.minCapacity
            d_513___mcc_h15_ = source38_.minOperands
            d_514___mcc_h16_ = source38_.pushes
            d_515___mcc_h17_ = source38_.pops
            d_516_pops_ = d_515___mcc_h17_
            d_517_pushes_ = d_514___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda9_(d_519_pops_, d_520_pushes_):
                    def lambda10_(d_521_pos_):
                        return ((d_521_pos_) + (d_519_pops_)) - (d_520_pushes_)

                    return lambda10_

                d_518_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda9_(d_516_pops_, d_517_pushes_))
                return WeakPre.Cond_StCond(d_518_shiftBy_, (c).TrackedVals())
        elif source38_.is_KeccakOp:
            d_522___mcc_h18_ = source38_.name
            d_523___mcc_h19_ = source38_.opcode
            d_524___mcc_h20_ = source38_.minCapacity
            d_525___mcc_h21_ = source38_.minOperands
            d_526___mcc_h22_ = source38_.pushes
            d_527___mcc_h23_ = source38_.pops
            d_528_pops_ = d_527___mcc_h23_
            d_529_pushes_ = d_526___mcc_h22_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda11_(d_531_pos_):
                    return (d_531_pos_) + (1)

                d_530_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda11_)
                return WeakPre.Cond_StCond(d_530_shiftByOne_, (c).TrackedVals())
        elif source38_.is_EnvOp:
            d_532___mcc_h24_ = source38_.name
            d_533___mcc_h25_ = source38_.opcode
            d_534___mcc_h26_ = source38_.minCapacity
            d_535___mcc_h27_ = source38_.minOperands
            d_536___mcc_h28_ = source38_.pushes
            d_537___mcc_h29_ = source38_.pops
            d_538_pops_ = d_537___mcc_h29_
            d_539_pushes_ = d_536___mcc_h28_
            if ((d_539_pushes_) == (1)) and ((d_538_pops_) == (0)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda12_(d_541_pos_):
                        return (d_541_pos_) - (1)

                    d_540_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda12_)
                    return WeakPre.Cond_StCond(d_540_shiftByOne_, (c).TrackedVals())
            elif ((d_539_pushes_) == (1)) and ((d_538_pops_) == (1)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
            elif True:
                def lambda13_(d_543_pops_, d_544_pushes_):
                    def lambda14_(d_545_pos_):
                        return ((d_545_pos_) + (d_543_pops_)) - (d_544_pushes_)

                    return lambda14_

                d_542_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda13_(d_538_pops_, d_539_pushes_))
                return WeakPre.Cond_StCond(d_542_shiftBy_, (c).TrackedVals())
        elif source38_.is_MemOp:
            d_546___mcc_h30_ = source38_.name
            d_547___mcc_h31_ = source38_.opcode
            d_548___mcc_h32_ = source38_.minCapacity
            d_549___mcc_h33_ = source38_.minOperands
            d_550___mcc_h34_ = source38_.pushes
            d_551___mcc_h35_ = source38_.pops
            d_552_pops_ = d_551___mcc_h35_
            d_553_pushes_ = d_550___mcc_h34_
            if (d_553_pushes_) == (0):
                def lambda15_(d_555_pos_):
                    return (d_555_pos_) + (2)

                d_554_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda15_)
                return WeakPre.Cond_StCond(d_554_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source38_.is_StorageOp:
            d_556___mcc_h36_ = source38_.name
            d_557___mcc_h37_ = source38_.opcode
            d_558___mcc_h38_ = source38_.minCapacity
            d_559___mcc_h39_ = source38_.minOperands
            d_560___mcc_h40_ = source38_.pushes
            d_561___mcc_h41_ = source38_.pops
            d_562_pops_ = d_561___mcc_h41_
            d_563_pushes_ = d_560___mcc_h40_
            if (d_563_pushes_) == (0):
                def lambda16_(d_565_pos_):
                    return (d_565_pos_) + (2)

                d_564_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                return WeakPre.Cond_StCond(d_564_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source38_.is_JumpOp:
            d_566___mcc_h42_ = source38_.name
            d_567___mcc_h43_ = source38_.opcode
            d_568___mcc_h44_ = source38_.minCapacity
            d_569___mcc_h45_ = source38_.minOperands
            d_570___mcc_h46_ = source38_.pushes
            d_571___mcc_h47_ = source38_.pops
            d_572_opcode_ = d_567___mcc_h43_
            if (d_572_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_572_opcode_)) and ((d_572_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_573_k_ = ((d_572_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda17_(d_575_k_):
                    def lambda18_(d_576_pos_):
                        return (d_576_pos_) + (d_575_k_)

                    return lambda18_

                d_574_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda17_(d_573_k_))
                return WeakPre.Cond_StCond(d_574_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source38_.is_RunOp:
            d_577___mcc_h48_ = source38_.name
            d_578___mcc_h49_ = source38_.opcode
            d_579___mcc_h50_ = source38_.minCapacity
            d_580___mcc_h51_ = source38_.minOperands
            d_581___mcc_h52_ = source38_.pushes
            d_582___mcc_h53_ = source38_.pops
            d_583_opcode_ = d_578___mcc_h49_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda19_(d_585_pos_):
                    return (d_585_pos_) - (1)

                d_584_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda19_)
                return WeakPre.Cond_StCond(d_584_shiftByOne_, (c).TrackedVals())
        elif source38_.is_StackOp:
            d_586___mcc_h54_ = source38_.name
            d_587___mcc_h55_ = source38_.opcode
            d_588___mcc_h56_ = source38_.minCapacity
            d_589___mcc_h57_ = source38_.minOperands
            d_590___mcc_h58_ = source38_.pushes
            d_591___mcc_h59_ = source38_.pops
            d_592_opcode_ = d_587___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_592_opcode_)) and ((d_592_opcode_) <= (EVMConstants.default__.PUSH32)):
                source39_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source39_.is_None:
                    def lambda20_(d_594_pos_):
                        return (d_594_pos_) - (1)

                    d_593_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda20_)
                    return WeakPre.Cond_StCond(d_593_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_595___mcc_h72_ = source39_.v
                    d_596_i_ = d_595___mcc_h72_
                    d_597_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_598___v142_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_596_i_)) == ((d_597_argVal_).Extract()):
                        d_599_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_596_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_596_i_) + (1)::]))
                        if (len(d_599_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda21_(d_601_pos_):
                                return (d_601_pos_) - (1)

                            d_600_shiftByMinusOne_ = MiscTypes.default__.Map(d_599_filtered_, lambda21_)
                            return WeakPre.Cond_StCond(d_600_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_596_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_596_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_592_opcode_)) and ((d_592_opcode_) <= (EVMConstants.default__.DUP16)):
                source40_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source40_.is_None:
                    def lambda22_(d_603_pos_):
                        return (d_603_pos_) - (1)

                    d_602_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda22_)
                    return WeakPre.Cond_StCond(d_602_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_604___mcc_h73_ = source40_.v
                    d_605_index0_ = d_604___mcc_h73_
                    source41_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_592_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source41_.is_None:
                        def lambda23_(d_607_opcode_):
                            def lambda24_(d_608_pos_):
                                return ((d_607_opcode_) - (EVMConstants.default__.DUP1) if (d_608_pos_) == (0) else (d_608_pos_) - (1))

                            return lambda24_

                        d_606_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda23_(d_592_opcode_))
                        return WeakPre.Cond_StCond(d_606_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_609___mcc_h74_ = source41_.v
                        d_610_index_ = d_609___mcc_h74_
                        if ((c).TrackedValAt(d_605_index0_)) == ((c).TrackedValAt(d_610_index_)):
                            d_611_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_605_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_605_index0_) + (1)::]))
                            def lambda25_(d_613_pos_):
                                return (d_613_pos_) - (1)

                            d_612_shiftByMinusOne_ = MiscTypes.default__.Map(d_611_filtered_, lambda25_)
                            return WeakPre.Cond_StCond(d_612_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_605_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_605_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_592_opcode_)) and ((d_592_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_614_k_ = ((d_592_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda26_(d_616_k_):
                    def lambda27_(d_617_pos_):
                        return (d_616_k_ if (d_617_pos_) == (0) else (0 if (d_617_pos_) == (d_616_k_) else d_617_pos_))

                    return lambda27_

                d_615_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda26_(d_614_k_))
                return WeakPre.Cond_StCond(d_615_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda28_(d_619_i_):
                    return (d_619_i_) + (1)

                d_618_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda28_)
                return WeakPre.Cond_StCond(d_618_shiftByOne_, (c).TrackedVals())
        elif source38_.is_LogOp:
            d_620___mcc_h60_ = source38_.name
            d_621___mcc_h61_ = source38_.opcode
            d_622___mcc_h62_ = source38_.minCapacity
            d_623___mcc_h63_ = source38_.minOperands
            d_624___mcc_h64_ = source38_.pushes
            d_625___mcc_h65_ = source38_.pops
            d_626_pops_ = d_625___mcc_h65_
            d_627_pushes_ = d_624___mcc_h64_
            d_628_opcode_ = d_621___mcc_h61_
            def lambda29_(d_630_pops_):
                def lambda30_(d_631_pos_):
                    return (d_631_pos_) + (d_630_pops_)

                return lambda30_

            d_629_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda29_(d_626_pops_))
            return WeakPre.Cond_StCond(d_629_shiftBy_, (c).TrackedVals())
        elif True:
            d_632___mcc_h66_ = source38_.name
            d_633___mcc_h67_ = source38_.opcode
            d_634___mcc_h68_ = source38_.minCapacity
            d_635___mcc_h69_ = source38_.minOperands
            d_636___mcc_h70_ = source38_.pushes
            d_637___mcc_h71_ = source38_.pops
            d_638_pops_ = d_637___mcc_h71_
            d_639_pushes_ = d_636___mcc_h70_
            d_640_opcode_ = d_633___mcc_h67_
            if (d_639_pushes_) == (0):
                def lambda31_(d_642_pops_):
                    def lambda32_(d_643_pos_):
                        return (d_643_pos_) + (d_642_pops_)

                    return lambda32_

                d_641_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda31_(d_638_pops_))
                return WeakPre.Cond_StCond(d_641_shiftBy_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda33_(d_645_pops_):
                        def lambda34_(d_646_pos_):
                            return (d_646_pos_) + (d_645_pops_)

                        return lambda34_

                    d_644_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda33_(d_638_pops_))
                    return WeakPre.Cond_StCond(d_644_shiftBy_, (c).TrackedVals())


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

