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
        d_201_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_202___v149_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_201_pad_) + (xc))).Extract()

    @staticmethod
    def ToDot(xi):
        d_203___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_203___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_203___accumulator_ = (d_203___accumulator_) + (((xi)[0]).ToHTML())
                    in38_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in38_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Colours(i):
        source34_ = (i).op
        if source34_.is_ArithOp:
            d_204___mcc_h0_ = source34_.name
            d_205___mcc_h1_ = source34_.opcode
            d_206___mcc_h2_ = source34_.minCapacity
            d_207___mcc_h3_ = source34_.minOperands
            d_208___mcc_h4_ = source34_.pushes
            d_209___mcc_h5_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#316152")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#c6eb76")))
        elif source34_.is_CompOp:
            d_210___mcc_h6_ = source34_.name
            d_211___mcc_h7_ = source34_.opcode
            d_212___mcc_h8_ = source34_.minCapacity
            d_213___mcc_h9_ = source34_.minOperands
            d_214___mcc_h10_ = source34_.pushes
            d_215___mcc_h11_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkgoldenrod")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "bisque")))
        elif source34_.is_BitwiseOp:
            d_216___mcc_h12_ = source34_.name
            d_217___mcc_h13_ = source34_.opcode
            d_218___mcc_h14_ = source34_.minCapacity
            d_219___mcc_h15_ = source34_.minOperands
            d_220___mcc_h16_ = source34_.pushes
            d_221___mcc_h17_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "orange")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#f3f383")))
        elif source34_.is_KeccakOp:
            d_222___mcc_h18_ = source34_.name
            d_223___mcc_h19_ = source34_.opcode
            d_224___mcc_h20_ = source34_.minCapacity
            d_225___mcc_h21_ = source34_.minOperands
            d_226___mcc_h22_ = source34_.pushes
            d_227___mcc_h23_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "grey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "linen")))
        elif source34_.is_EnvOp:
            d_228___mcc_h24_ = source34_.name
            d_229___mcc_h25_ = source34_.opcode
            d_230___mcc_h26_ = source34_.minCapacity
            d_231___mcc_h27_ = source34_.minOperands
            d_232___mcc_h28_ = source34_.pushes
            d_233___mcc_h29_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkslategrey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightgrey")))
        elif source34_.is_MemOp:
            d_234___mcc_h30_ = source34_.name
            d_235___mcc_h31_ = source34_.opcode
            d_236___mcc_h32_ = source34_.minCapacity
            d_237___mcc_h33_ = source34_.minOperands
            d_238___mcc_h34_ = source34_.pushes
            d_239___mcc_h35_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "wheat")))
        elif source34_.is_StorageOp:
            d_240___mcc_h36_ = source34_.name
            d_241___mcc_h37_ = source34_.opcode
            d_242___mcc_h38_ = source34_.minCapacity
            d_243___mcc_h39_ = source34_.minOperands
            d_244___mcc_h40_ = source34_.pushes
            d_245___mcc_h41_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "fuchsia")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "mistyrose")))
        elif source34_.is_JumpOp:
            d_246___mcc_h42_ = source34_.name
            d_247___mcc_h43_ = source34_.opcode
            d_248___mcc_h44_ = source34_.minCapacity
            d_249___mcc_h45_ = source34_.minOperands
            d_250___mcc_h46_ = source34_.pushes
            d_251___mcc_h47_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "purple")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "thistle")))
        elif source34_.is_RunOp:
            d_252___mcc_h48_ = source34_.name
            d_253___mcc_h49_ = source34_.opcode
            d_254___mcc_h50_ = source34_.minCapacity
            d_255___mcc_h51_ = source34_.minOperands
            d_256___mcc_h52_ = source34_.pushes
            d_257___mcc_h53_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tan")))
        elif source34_.is_StackOp:
            d_258___mcc_h54_ = source34_.name
            d_259___mcc_h55_ = source34_.opcode
            d_260___mcc_h56_ = source34_.minCapacity
            d_261___mcc_h57_ = source34_.minOperands
            d_262___mcc_h58_ = source34_.pushes
            d_263___mcc_h59_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "royalblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "powderblue")))
        elif source34_.is_LogOp:
            d_264___mcc_h60_ = source34_.name
            d_265___mcc_h61_ = source34_.opcode
            d_266___mcc_h62_ = source34_.minCapacity
            d_267___mcc_h63_ = source34_.minOperands
            d_268___mcc_h64_ = source34_.pushes
            d_269___mcc_h65_ = source34_.pops
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "cornflowerblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lavender")))
        elif True:
            d_270___mcc_h66_ = source34_.name
            d_271___mcc_h67_ = source34_.opcode
            d_272___mcc_h68_ = source34_.minCapacity
            d_273___mcc_h69_ = source34_.minOperands
            d_274___mcc_h70_ = source34_.pushes
            d_275___mcc_h71_ = source34_.pops
            d_276_opcode_ = d_271___mcc_h67_
            if ((d_276_opcode_) == (EVMConstants.default__.STOP)) or ((d_276_opcode_) == (EVMConstants.default__.REVERT)):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "brown")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightsalmon")))
            elif (d_276_opcode_) == (EVMConstants.default__.RETURN):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "teal")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "greenyellow")))
            elif ((((d_276_opcode_) == (EVMConstants.default__.CALL)) or ((d_276_opcode_) == (EVMConstants.default__.CALLCODE))) or ((d_276_opcode_) == (EVMConstants.default__.DELEGATECALL))) or ((d_276_opcode_) == (EVMConstants.default__.STATICCALL)):
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
        d_277_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_277_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_277_x_) if (len(d_277_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def Equiv(self, i):
        return (((self).op) == ((i).op)) and (((self).arg) == ((i).arg))

    def ToHTML(self):
        d_278_x_ = (self).arg
        d_279_cols_ = default__.Colours(self)
        d_280_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_281___v0_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_282_insText_ = (((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_279_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_278_x_) if (((self).op).opcode) == (EVMConstants.default__.INVALID) else (((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_279_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_278_x_) if (len(d_278_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))))
        return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (d_280_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":")))) + (d_282_insText_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))

    def ToHTMLTable(self, entryPortTag, exitPortTag):
        d_283_cols_ = default__.Colours(self)
        d_284_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_285___v1_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_286_gasLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981; "))
        d_287_oplineTD_ = ((((((((((((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"7\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: "))) + (EVMToolTips.default__.Gas(((self).op).opcode))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " \" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "target=\"_blank\" href=\"")))) + (EVMToolTips.default__.gasRefLine)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (d_286_gasLine_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" ")))) + (entryPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x")))) + (d_284_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " </TD>\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")))) + ((d_283_cols_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" align=\"left\" cellpadding=\"3\" ")))) + (exitPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"")))) + (EVMToolTips.default__.bytecodeRefLine)) + (Int.default__.NatToString((EVMToolTips.default__.ToolTip(((self).op).opcode))[1]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" target=\"_blank\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " tooltip=\"")))) + ((EVMToolTips.default__.ToolTip(((self).op).opcode))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\"")))) + ((d_283_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))
        d_288_arglineTD_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" align=\"left\">"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  0x")))) + ((self).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>"))) if (len((self).arg)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_289_lineTR_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR>"))) + (d_287_oplineTD_)) + (d_288_arglineTD_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR>")))
        d_290_itemTable_ = ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE  border=\"0\" cellpadding=\"0\" cellborder=\"0\" CELLSPACING=\"1\">"))) + (d_289_lineTR_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>")))
        return d_290_itemTable_

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
        source35_ = (self).op
        if source35_.is_ArithOp:
            d_291___mcc_h0_ = source35_.name
            d_292___mcc_h1_ = source35_.opcode
            d_293___mcc_h2_ = source35_.minCapacity
            d_294___mcc_h3_ = source35_.minOperands
            d_295___mcc_h4_ = source35_.pushes
            d_296___mcc_h5_ = source35_.pops
            d_297_pops_ = d_296___mcc_h5_
            d_298_pushes_ = d_295___mcc_h4_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        elif source35_.is_CompOp:
            d_299___mcc_h6_ = source35_.name
            d_300___mcc_h7_ = source35_.opcode
            d_301___mcc_h8_ = source35_.minCapacity
            d_302___mcc_h9_ = source35_.minOperands
            d_303___mcc_h10_ = source35_.pushes
            d_304___mcc_h11_ = source35_.pops
            d_305_pops_ = d_304___mcc_h11_
            d_306_pushes_ = d_303___mcc_h10_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_305_pops_)) - (d_306_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        elif source35_.is_BitwiseOp:
            d_307___mcc_h12_ = source35_.name
            d_308___mcc_h13_ = source35_.opcode
            d_309___mcc_h14_ = source35_.minCapacity
            d_310___mcc_h15_ = source35_.minOperands
            d_311___mcc_h16_ = source35_.pushes
            d_312___mcc_h17_ = source35_.pops
            d_313_pops_ = d_312___mcc_h17_
            d_314_pushes_ = d_311___mcc_h16_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right(((pos_k) + (d_313_pops_)) - (d_314_pushes_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Bitwise operator with target 0"))))
        elif source35_.is_KeccakOp:
            d_315___mcc_h18_ = source35_.name
            d_316___mcc_h19_ = source35_.opcode
            d_317___mcc_h20_ = source35_.minCapacity
            d_318___mcc_h21_ = source35_.minOperands
            d_319___mcc_h22_ = source35_.pushes
            d_320___mcc_h23_ = source35_.pops
            d_321_pops_ = d_320___mcc_h23_
            d_322_pushes_ = d_319___mcc_h22_
            if (pos_k) >= (1):
                return MiscTypes.Either_Right((pos_k) + (1))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Keccak operator with target 0"))))
        elif source35_.is_EnvOp:
            d_323___mcc_h24_ = source35_.name
            d_324___mcc_h25_ = source35_.opcode
            d_325___mcc_h26_ = source35_.minCapacity
            d_326___mcc_h27_ = source35_.minOperands
            d_327___mcc_h28_ = source35_.pushes
            d_328___mcc_h29_ = source35_.pops
            d_329_pops_ = d_328___mcc_h29_
            d_330_pushes_ = d_327___mcc_h28_
            if ((d_330_pushes_) == (1)) and ((d_329_pops_) == (0)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((d_330_pushes_) == (1)) and ((d_329_pops_) == (1)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
            elif True:
                return MiscTypes.Either_Right(((pos_k) + (d_329_pops_)) - (d_330_pushes_))
        elif source35_.is_MemOp:
            d_331___mcc_h30_ = source35_.name
            d_332___mcc_h31_ = source35_.opcode
            d_333___mcc_h32_ = source35_.minCapacity
            d_334___mcc_h33_ = source35_.minOperands
            d_335___mcc_h34_ = source35_.pushes
            d_336___mcc_h35_ = source35_.pops
            d_337_pops_ = d_336___mcc_h35_
            d_338_pushes_ = d_335___mcc_h34_
            if (d_338_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Mem operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source35_.is_StorageOp:
            d_339___mcc_h36_ = source35_.name
            d_340___mcc_h37_ = source35_.opcode
            d_341___mcc_h38_ = source35_.minCapacity
            d_342___mcc_h39_ = source35_.minOperands
            d_343___mcc_h40_ = source35_.pushes
            d_344___mcc_h41_ = source35_.pops
            d_345_pops_ = d_344___mcc_h41_
            d_346_pushes_ = d_343___mcc_h40_
            if (d_346_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (2))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Storage operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right(pos_k)
        elif source35_.is_JumpOp:
            d_347___mcc_h42_ = source35_.name
            d_348___mcc_h43_ = source35_.opcode
            d_349___mcc_h44_ = source35_.minCapacity
            d_350___mcc_h45_ = source35_.minOperands
            d_351___mcc_h46_ = source35_.pushes
            d_352___mcc_h47_ = source35_.pops
            d_353_opcode_ = d_348___mcc_h43_
            if (d_353_opcode_) == (EVMConstants.default__.JUMPDEST):
                return MiscTypes.Either_Right(pos_k)
            elif ((EVMConstants.default__.JUMP) <= (d_353_opcode_)) and ((d_353_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_354_k_ = ((d_353_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                return MiscTypes.Either_Right((pos_k) + (d_354_k_))
            elif True:
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        elif source35_.is_RunOp:
            d_355___mcc_h48_ = source35_.name
            d_356___mcc_h49_ = source35_.opcode
            d_357___mcc_h50_ = source35_.minCapacity
            d_358___mcc_h51_ = source35_.minOperands
            d_359___mcc_h52_ = source35_.pushes
            d_360___mcc_h53_ = source35_.pops
            d_361_pops_ = d_360___mcc_h53_
            d_362_pushes_ = d_359___mcc_h52_
            if (pos_k) == (0):
                return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Run operator with target 0"))))
            elif True:
                return MiscTypes.Either_Right((pos_k) - (1))
        elif source35_.is_StackOp:
            d_363___mcc_h54_ = source35_.name
            d_364___mcc_h55_ = source35_.opcode
            d_365___mcc_h56_ = source35_.minCapacity
            d_366___mcc_h57_ = source35_.minOperands
            d_367___mcc_h58_ = source35_.pushes
            d_368___mcc_h59_ = source35_.pops
            d_369_opcode_ = d_364___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_369_opcode_)) and ((d_369_opcode_) <= (EVMConstants.default__.PUSH32)):
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
            elif ((EVMConstants.default__.DUP1) <= (d_369_opcode_)) and ((d_369_opcode_) <= (EVMConstants.default__.DUP16)):
                return MiscTypes.Either_Right(((d_369_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
            elif ((EVMConstants.default__.SWAP1) <= (d_369_opcode_)) and ((d_369_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_370_k_ = ((d_369_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                return MiscTypes.Either_Right((d_370_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_370_k_) else pos_k)))
            elif True:
                return MiscTypes.Either_Right((pos_k) + (1))
        elif source35_.is_LogOp:
            d_371___mcc_h60_ = source35_.name
            d_372___mcc_h61_ = source35_.opcode
            d_373___mcc_h62_ = source35_.minCapacity
            d_374___mcc_h63_ = source35_.minOperands
            d_375___mcc_h64_ = source35_.pushes
            d_376___mcc_h65_ = source35_.pops
            d_377_pops_ = d_376___mcc_h65_
            d_378_pushes_ = d_375___mcc_h64_
            return MiscTypes.Either_Right((pos_k) + (d_377_pops_))
        elif True:
            d_379___mcc_h66_ = source35_.name
            d_380___mcc_h67_ = source35_.opcode
            d_381___mcc_h68_ = source35_.minCapacity
            d_382___mcc_h69_ = source35_.minOperands
            d_383___mcc_h70_ = source35_.pushes
            d_384___mcc_h71_ = source35_.pops
            d_385_pops_ = d_384___mcc_h71_
            d_386_pushes_ = d_383___mcc_h70_
            if (d_386_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (d_385_pops_))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Sys operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) + (d_385_pops_))

    def NextState(self, s, jumpDests, exit):
        source36_ = (self).op
        if source36_.is_ArithOp:
            d_387___mcc_h0_ = source36_.name
            d_388___mcc_h1_ = source36_.opcode
            d_389___mcc_h2_ = source36_.minCapacity
            d_390___mcc_h3_ = source36_.minOperands
            d_391___mcc_h4_ = source36_.pushes
            d_392___mcc_h5_ = source36_.pops
            d_393_pops_ = d_392___mcc_h5_
            d_394_pushes_ = d_391___mcc_h4_
            if ((s).Size()) >= (d_393_pops_):
                return (((s).PopN(d_393_pops_)).PushNRandom(d_394_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source36_.is_CompOp:
            d_395___mcc_h6_ = source36_.name
            d_396___mcc_h7_ = source36_.opcode
            d_397___mcc_h8_ = source36_.minCapacity
            d_398___mcc_h9_ = source36_.minOperands
            d_399___mcc_h10_ = source36_.pushes
            d_400___mcc_h11_ = source36_.pops
            d_401_pops_ = d_400___mcc_h11_
            d_402_pushes_ = d_399___mcc_h10_
            if ((s).Size()) >= (d_401_pops_):
                return (((s).PopN(d_401_pops_)).PushNRandom(d_402_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source36_.is_BitwiseOp:
            d_403___mcc_h12_ = source36_.name
            d_404___mcc_h13_ = source36_.opcode
            d_405___mcc_h14_ = source36_.minCapacity
            d_406___mcc_h15_ = source36_.minOperands
            d_407___mcc_h16_ = source36_.pushes
            d_408___mcc_h17_ = source36_.pops
            d_409_pops_ = d_408___mcc_h17_
            d_410_pushes_ = d_407___mcc_h16_
            if ((s).Size()) >= (d_409_pops_):
                return (((s).PopN(d_409_pops_)).PushNRandom(d_410_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source36_.is_KeccakOp:
            d_411___mcc_h18_ = source36_.name
            d_412___mcc_h19_ = source36_.opcode
            d_413___mcc_h20_ = source36_.minCapacity
            d_414___mcc_h21_ = source36_.minOperands
            d_415___mcc_h22_ = source36_.pushes
            d_416___mcc_h23_ = source36_.pops
            d_417_pops_ = d_416___mcc_h23_
            d_418_pushes_ = d_415___mcc_h22_
            if ((s).Size()) >= (2):
                return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        elif source36_.is_EnvOp:
            d_419___mcc_h24_ = source36_.name
            d_420___mcc_h25_ = source36_.opcode
            d_421___mcc_h26_ = source36_.minCapacity
            d_422___mcc_h27_ = source36_.minOperands
            d_423___mcc_h28_ = source36_.pushes
            d_424___mcc_h29_ = source36_.pops
            d_425_pops_ = d_424___mcc_h29_
            d_426_pushes_ = d_423___mcc_h28_
            if ((s).Size()) >= (d_425_pops_):
                return (((s).PopN(d_425_pops_)).PushNRandom(d_426_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        elif source36_.is_MemOp:
            d_427___mcc_h30_ = source36_.name
            d_428___mcc_h31_ = source36_.opcode
            d_429___mcc_h32_ = source36_.minCapacity
            d_430___mcc_h33_ = source36_.minOperands
            d_431___mcc_h34_ = source36_.pushes
            d_432___mcc_h35_ = source36_.pops
            d_433_pops_ = d_432___mcc_h35_
            d_434_pushes_ = d_431___mcc_h34_
            if ((s).Size()) >= (d_433_pops_):
                return (((s).PopN(d_433_pops_)).PushNRandom(d_434_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        elif source36_.is_StorageOp:
            d_435___mcc_h36_ = source36_.name
            d_436___mcc_h37_ = source36_.opcode
            d_437___mcc_h38_ = source36_.minCapacity
            d_438___mcc_h39_ = source36_.minOperands
            d_439___mcc_h40_ = source36_.pushes
            d_440___mcc_h41_ = source36_.pops
            d_441_pops_ = d_440___mcc_h41_
            d_442_pushes_ = d_439___mcc_h40_
            if ((s).Size()) >= (d_441_pops_):
                return (((s).PopN(d_441_pops_)).PushNRandom(d_442_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        elif source36_.is_JumpOp:
            d_443___mcc_h42_ = source36_.name
            d_444___mcc_h43_ = source36_.opcode
            d_445___mcc_h44_ = source36_.minCapacity
            d_446___mcc_h45_ = source36_.minOperands
            d_447___mcc_h46_ = source36_.pushes
            d_448___mcc_h47_ = source36_.pops
            d_449_pops_ = d_448___mcc_h47_
            d_450_pushes_ = d_447___mcc_h46_
            d_451_opcode_ = d_444___mcc_h43_
            if (d_451_opcode_) == (EVMConstants.default__.JUMPDEST):
                return (s).Skip(1)
            elif (d_451_opcode_) == (EVMConstants.default__.JUMP):
                if ((s).Size()) >= (1):
                    source37_ = (s).Peek(0)
                    if source37_.is_Value:
                        d_452___mcc_h72_ = source37_.v
                        d_453_v_ = d_452___mcc_h72_
                        return ((s).Pop()).Goto(d_453_v_)
                    elif True:
                        d_454___mcc_h73_ = source37_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() unknown PC error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
            elif (d_451_opcode_) == (EVMConstants.default__.JUMPI):
                if ((s).Size()) >= (2):
                    source38_ = (s).Peek(0)
                    if source38_.is_Value:
                        d_455___mcc_h74_ = source38_.v
                        d_456_v_ = d_455___mcc_h74_
                        if (exit) >= (1):
                            return ((s).PopN(2)).Goto(d_456_v_)
                        elif True:
                            return ((s).PopN(2)).Skip(1)
                    elif True:
                        d_457___mcc_h75_ = source38_.s
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        elif source36_.is_RunOp:
            d_458___mcc_h48_ = source36_.name
            d_459___mcc_h49_ = source36_.opcode
            d_460___mcc_h50_ = source36_.minCapacity
            d_461___mcc_h51_ = source36_.minOperands
            d_462___mcc_h52_ = source36_.pushes
            d_463___mcc_h53_ = source36_.pops
            d_464_pops_ = d_463___mcc_h53_
            d_465_pushes_ = d_462___mcc_h52_
            return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
        elif source36_.is_StackOp:
            d_466___mcc_h54_ = source36_.name
            d_467___mcc_h55_ = source36_.opcode
            d_468___mcc_h56_ = source36_.minCapacity
            d_469___mcc_h57_ = source36_.minOperands
            d_470___mcc_h58_ = source36_.pushes
            d_471___mcc_h59_ = source36_.pops
            d_472_pops_ = d_471___mcc_h59_
            d_473_pushes_ = d_470___mcc_h58_
            d_474_opcode_ = d_467___mcc_h55_
            if ((d_474_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1)):
                return ((s).Pop()).Skip(1)
            elif ((EVMConstants.default__.PUSH0) <= (d_474_opcode_)) and ((d_474_opcode_) <= (EVMConstants.default__.PUSH32)):
                d_475_valToPush_ = (StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)) if (default__.GetArgValuePush((self).arg)) in (jumpDests) else StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))
                return ((s).Push(d_475_valToPush_)).Skip((1) + ((d_474_opcode_) - (EVMConstants.default__.PUSH0)))
            elif (((EVMConstants.default__.DUP1) <= (d_474_opcode_)) and ((d_474_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_474_opcode_) - (EVMConstants.default__.DUP1)) + (1))):
                return ((s).Dup(((d_474_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
            elif (((EVMConstants.default__.SWAP1) <= (d_474_opcode_)) and ((d_474_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_474_opcode_) - (EVMConstants.default__.SWAP1)) + (1))):
                return ((s).Swap(((d_474_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        elif source36_.is_LogOp:
            d_476___mcc_h60_ = source36_.name
            d_477___mcc_h61_ = source36_.opcode
            d_478___mcc_h62_ = source36_.minCapacity
            d_479___mcc_h63_ = source36_.minOperands
            d_480___mcc_h64_ = source36_.pushes
            d_481___mcc_h65_ = source36_.pops
            d_482_pops_ = d_481___mcc_h65_
            d_483_pushes_ = d_480___mcc_h64_
            if ((s).Size()) >= (d_482_pops_):
                return ((s).PopN(d_482_pops_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        elif True:
            d_484___mcc_h66_ = source36_.name
            d_485___mcc_h67_ = source36_.opcode
            d_486___mcc_h68_ = source36_.minCapacity
            d_487___mcc_h69_ = source36_.minOperands
            d_488___mcc_h70_ = source36_.pushes
            d_489___mcc_h71_ = source36_.pops
            d_490_pops_ = d_489___mcc_h71_
            d_491_pushes_ = d_488___mcc_h70_
            d_492_op_ = d_485___mcc_h67_
            if (((d_492_op_) == (EVMConstants.default__.INVALID)) or ((d_492_op_) == (EVMConstants.default__.STOP))) or ((d_492_op_) == (EVMConstants.default__.REVERT)):
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))
            elif ((s).Size()) >= (d_490_pops_):
                return (((s).PopN(d_490_pops_)).PushNRandom(d_491_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source39_ = (self).op
        if source39_.is_ArithOp:
            d_493___mcc_h0_ = source39_.name
            d_494___mcc_h1_ = source39_.opcode
            d_495___mcc_h2_ = source39_.minCapacity
            d_496___mcc_h3_ = source39_.minOperands
            d_497___mcc_h4_ = source39_.pushes
            d_498___mcc_h5_ = source39_.pops
            d_499_pops_ = d_498___mcc_h5_
            d_500_pushes_ = d_497___mcc_h4_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda6_(d_502_pos_):
                    return (d_502_pos_) + (1)

                d_501_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_)
                return WeakPre.Cond_StCond(d_501_shiftByOne_, (c).TrackedVals())
        elif source39_.is_CompOp:
            d_503___mcc_h6_ = source39_.name
            d_504___mcc_h7_ = source39_.opcode
            d_505___mcc_h8_ = source39_.minCapacity
            d_506___mcc_h9_ = source39_.minOperands
            d_507___mcc_h10_ = source39_.pushes
            d_508___mcc_h11_ = source39_.pops
            d_509_pops_ = d_508___mcc_h11_
            d_510_pushes_ = d_507___mcc_h10_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda7_(d_512_pops_, d_513_pushes_):
                    def lambda8_(d_514_pos_):
                        return ((d_514_pos_) + (d_512_pops_)) - (d_513_pushes_)

                    return lambda8_

                d_511_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda7_(d_509_pops_, d_510_pushes_))
                return WeakPre.Cond_StCond(d_511_shiftBy_, (c).TrackedVals())
        elif source39_.is_BitwiseOp:
            d_515___mcc_h12_ = source39_.name
            d_516___mcc_h13_ = source39_.opcode
            d_517___mcc_h14_ = source39_.minCapacity
            d_518___mcc_h15_ = source39_.minOperands
            d_519___mcc_h16_ = source39_.pushes
            d_520___mcc_h17_ = source39_.pops
            d_521_pops_ = d_520___mcc_h17_
            d_522_pushes_ = d_519___mcc_h16_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda9_(d_524_pops_, d_525_pushes_):
                    def lambda10_(d_526_pos_):
                        return ((d_526_pos_) + (d_524_pops_)) - (d_525_pushes_)

                    return lambda10_

                d_523_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda9_(d_521_pops_, d_522_pushes_))
                return WeakPre.Cond_StCond(d_523_shiftBy_, (c).TrackedVals())
        elif source39_.is_KeccakOp:
            d_527___mcc_h18_ = source39_.name
            d_528___mcc_h19_ = source39_.opcode
            d_529___mcc_h20_ = source39_.minCapacity
            d_530___mcc_h21_ = source39_.minOperands
            d_531___mcc_h22_ = source39_.pushes
            d_532___mcc_h23_ = source39_.pops
            d_533_pops_ = d_532___mcc_h23_
            d_534_pushes_ = d_531___mcc_h22_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda11_(d_536_pos_):
                    return (d_536_pos_) + (1)

                d_535_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda11_)
                return WeakPre.Cond_StCond(d_535_shiftByOne_, (c).TrackedVals())
        elif source39_.is_EnvOp:
            d_537___mcc_h24_ = source39_.name
            d_538___mcc_h25_ = source39_.opcode
            d_539___mcc_h26_ = source39_.minCapacity
            d_540___mcc_h27_ = source39_.minOperands
            d_541___mcc_h28_ = source39_.pushes
            d_542___mcc_h29_ = source39_.pops
            d_543_pops_ = d_542___mcc_h29_
            d_544_pushes_ = d_541___mcc_h28_
            if ((d_544_pushes_) == (1)) and ((d_543_pops_) == (0)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda12_(d_546_pos_):
                        return (d_546_pos_) - (1)

                    d_545_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda12_)
                    return WeakPre.Cond_StCond(d_545_shiftByOne_, (c).TrackedVals())
            elif ((d_544_pushes_) == (1)) and ((d_543_pops_) == (1)):
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
            elif True:
                def lambda13_(d_548_pops_, d_549_pushes_):
                    def lambda14_(d_550_pos_):
                        return ((d_550_pos_) + (d_548_pops_)) - (d_549_pushes_)

                    return lambda14_

                d_547_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda13_(d_543_pops_, d_544_pushes_))
                return WeakPre.Cond_StCond(d_547_shiftBy_, (c).TrackedVals())
        elif source39_.is_MemOp:
            d_551___mcc_h30_ = source39_.name
            d_552___mcc_h31_ = source39_.opcode
            d_553___mcc_h32_ = source39_.minCapacity
            d_554___mcc_h33_ = source39_.minOperands
            d_555___mcc_h34_ = source39_.pushes
            d_556___mcc_h35_ = source39_.pops
            d_557_pops_ = d_556___mcc_h35_
            d_558_pushes_ = d_555___mcc_h34_
            if (d_558_pushes_) == (0):
                def lambda15_(d_560_pos_):
                    return (d_560_pos_) + (2)

                d_559_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda15_)
                return WeakPre.Cond_StCond(d_559_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source39_.is_StorageOp:
            d_561___mcc_h36_ = source39_.name
            d_562___mcc_h37_ = source39_.opcode
            d_563___mcc_h38_ = source39_.minCapacity
            d_564___mcc_h39_ = source39_.minOperands
            d_565___mcc_h40_ = source39_.pushes
            d_566___mcc_h41_ = source39_.pops
            d_567_pops_ = d_566___mcc_h41_
            d_568_pushes_ = d_565___mcc_h40_
            if (d_568_pushes_) == (0):
                def lambda16_(d_570_pos_):
                    return (d_570_pos_) + (2)

                d_569_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                return WeakPre.Cond_StCond(d_569_shiftByTwo_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    return c
        elif source39_.is_JumpOp:
            d_571___mcc_h42_ = source39_.name
            d_572___mcc_h43_ = source39_.opcode
            d_573___mcc_h44_ = source39_.minCapacity
            d_574___mcc_h45_ = source39_.minOperands
            d_575___mcc_h46_ = source39_.pushes
            d_576___mcc_h47_ = source39_.pops
            d_577_opcode_ = d_572___mcc_h43_
            if (d_577_opcode_) == (EVMConstants.default__.JUMPDEST):
                return c
            elif ((EVMConstants.default__.JUMP) <= (d_577_opcode_)) and ((d_577_opcode_) <= (EVMConstants.default__.JUMPI)):
                d_578_k_ = ((d_577_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                def lambda17_(d_580_k_):
                    def lambda18_(d_581_pos_):
                        return (d_581_pos_) + (d_580_k_)

                    return lambda18_

                d_579_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda17_(d_578_k_))
                return WeakPre.Cond_StCond(d_579_shiftBy_, (c).TrackedVals())
            elif True:
                return WeakPre.Cond_StFalse()
        elif source39_.is_RunOp:
            d_582___mcc_h48_ = source39_.name
            d_583___mcc_h49_ = source39_.opcode
            d_584___mcc_h50_ = source39_.minCapacity
            d_585___mcc_h51_ = source39_.minOperands
            d_586___mcc_h52_ = source39_.pushes
            d_587___mcc_h53_ = source39_.pops
            d_588_opcode_ = d_583___mcc_h49_
            if (0) in ((c).TrackedPos()):
                return WeakPre.Cond_StFalse()
            elif True:
                def lambda19_(d_590_pos_):
                    return (d_590_pos_) - (1)

                d_589_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda19_)
                return WeakPre.Cond_StCond(d_589_shiftByOne_, (c).TrackedVals())
        elif source39_.is_StackOp:
            d_591___mcc_h54_ = source39_.name
            d_592___mcc_h55_ = source39_.opcode
            d_593___mcc_h56_ = source39_.minCapacity
            d_594___mcc_h57_ = source39_.minOperands
            d_595___mcc_h58_ = source39_.pushes
            d_596___mcc_h59_ = source39_.pops
            d_597_opcode_ = d_592___mcc_h55_
            if ((EVMConstants.default__.PUSH0) <= (d_597_opcode_)) and ((d_597_opcode_) <= (EVMConstants.default__.PUSH32)):
                source40_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source40_.is_None:
                    def lambda20_(d_599_pos_):
                        return (d_599_pos_) - (1)

                    d_598_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda20_)
                    return WeakPre.Cond_StCond(d_598_shiftByMinusOne_, (c).TrackedVals())
                elif True:
                    d_600___mcc_h72_ = source40_.v
                    d_601_i_ = d_600___mcc_h72_
                    d_602_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_603___v142_ in range((64) - (len((self).arg)))])) + ((self).arg))
                    if ((c).TrackedValAt(d_601_i_)) == ((d_602_argVal_).Extract()):
                        d_604_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_601_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_601_i_) + (1)::]))
                        if (len(d_604_filtered_)) == (0):
                            return WeakPre.Cond_StTrue()
                        elif True:
                            def lambda21_(d_606_pos_):
                                return (d_606_pos_) - (1)

                            d_605_shiftByMinusOne_ = MiscTypes.default__.Map(d_604_filtered_, lambda21_)
                            return WeakPre.Cond_StCond(d_605_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_601_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_601_i_) + (1)::])))
                    elif True:
                        return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.DUP1) <= (d_597_opcode_)) and ((d_597_opcode_) <= (EVMConstants.default__.DUP16)):
                source41_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                if source41_.is_None:
                    def lambda22_(d_608_pos_):
                        return (d_608_pos_) - (1)

                    d_607_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda22_)
                    return WeakPre.Cond_StCond(d_607_shiftByMinusOneButZero_, (c).TrackedVals())
                elif True:
                    d_609___mcc_h73_ = source41_.v
                    d_610_index0_ = d_609___mcc_h73_
                    source42_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_597_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                    if source42_.is_None:
                        def lambda23_(d_612_opcode_):
                            def lambda24_(d_613_pos_):
                                return ((d_612_opcode_) - (EVMConstants.default__.DUP1) if (d_613_pos_) == (0) else (d_613_pos_) - (1))

                            return lambda24_

                        d_611_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda23_(d_597_opcode_))
                        return WeakPre.Cond_StCond(d_611_shiftByMinusOneButZero_, (c).TrackedVals())
                    elif True:
                        d_614___mcc_h74_ = source42_.v
                        d_615_index_ = d_614___mcc_h74_
                        if ((c).TrackedValAt(d_610_index0_)) == ((c).TrackedValAt(d_615_index_)):
                            d_616_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_610_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_610_index0_) + (1)::]))
                            def lambda25_(d_618_pos_):
                                return (d_618_pos_) - (1)

                            d_617_shiftByMinusOne_ = MiscTypes.default__.Map(d_616_filtered_, lambda25_)
                            return WeakPre.Cond_StCond(d_617_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_610_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_610_index0_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
            elif ((EVMConstants.default__.SWAP1) <= (d_597_opcode_)) and ((d_597_opcode_) <= (EVMConstants.default__.SWAP16)):
                d_619_k_ = ((d_597_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                def lambda26_(d_621_k_):
                    def lambda27_(d_622_pos_):
                        return (d_621_k_ if (d_622_pos_) == (0) else (0 if (d_622_pos_) == (d_621_k_) else d_622_pos_))

                    return lambda27_

                d_620_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda26_(d_619_k_))
                return WeakPre.Cond_StCond(d_620_swapZeroAndk_, (c).TrackedVals())
            elif True:
                def lambda28_(d_624_i_):
                    return (d_624_i_) + (1)

                d_623_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda28_)
                return WeakPre.Cond_StCond(d_623_shiftByOne_, (c).TrackedVals())
        elif source39_.is_LogOp:
            d_625___mcc_h60_ = source39_.name
            d_626___mcc_h61_ = source39_.opcode
            d_627___mcc_h62_ = source39_.minCapacity
            d_628___mcc_h63_ = source39_.minOperands
            d_629___mcc_h64_ = source39_.pushes
            d_630___mcc_h65_ = source39_.pops
            d_631_pops_ = d_630___mcc_h65_
            d_632_pushes_ = d_629___mcc_h64_
            d_633_opcode_ = d_626___mcc_h61_
            def lambda29_(d_635_pops_):
                def lambda30_(d_636_pos_):
                    return (d_636_pos_) + (d_635_pops_)

                return lambda30_

            d_634_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda29_(d_631_pops_))
            return WeakPre.Cond_StCond(d_634_shiftBy_, (c).TrackedVals())
        elif True:
            d_637___mcc_h66_ = source39_.name
            d_638___mcc_h67_ = source39_.opcode
            d_639___mcc_h68_ = source39_.minCapacity
            d_640___mcc_h69_ = source39_.minOperands
            d_641___mcc_h70_ = source39_.pushes
            d_642___mcc_h71_ = source39_.pops
            d_643_pops_ = d_642___mcc_h71_
            d_644_pushes_ = d_641___mcc_h70_
            d_645_opcode_ = d_638___mcc_h67_
            if (d_644_pushes_) == (0):
                def lambda31_(d_647_pops_):
                    def lambda32_(d_648_pos_):
                        return (d_648_pos_) + (d_647_pops_)

                    return lambda32_

                d_646_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda31_(d_643_pops_))
                return WeakPre.Cond_StCond(d_646_shiftBy_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda33_(d_650_pops_):
                        def lambda34_(d_651_pos_):
                            return (d_651_pos_) + (d_650_pops_)

                        return lambda34_

                    d_649_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda33_(d_643_pops_))
                    return WeakPre.Cond_StCond(d_649_shiftBy_, (c).TrackedVals())


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

