import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import MiscTypes as MiscTypes
import Int as Int
import EVMConstants as EVMConstants
import EVMOpcodes as EVMOpcodes
import OpcodeDecoder as OpcodeDecoder
import Hex as Hex
import StackElement as StackElement
import WeakPre as WeakPre
import State as State
import EVMToolTips as EVMToolTips

# Module: Instructions

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetArgValuePush(xc):
        d_0_pad_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_1___v149_ in range((64) - (len(xc)))])
        return (Hex.default__.HexToU256((d_0_pad_) + (xc))).Extract()

    @staticmethod
    def ToDot(xi):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xi)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (((xi)[0]).ToHTML())
                    in0_ = _dafny.SeqWithoutIsStrInference((xi)[1::])
                    xi = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Colours(i):
        source0_ = (i).op
        if True:
            if source0_.is_ArithOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#316152")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#c6eb76")))
        if True:
            if source0_.is_CompOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkgoldenrod")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "bisque")))
        if True:
            if source0_.is_BitwiseOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "orange")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "#f3f383")))
        if True:
            if source0_.is_KeccakOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "grey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "linen")))
        if True:
            if source0_.is_EnvOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "darkslategrey")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightgrey")))
        if True:
            if source0_.is_MemOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "wheat")))
        if True:
            if source0_.is_StorageOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "fuchsia")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "mistyrose")))
        if True:
            if source0_.is_JumpOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "purple")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "thistle")))
        if True:
            if source0_.is_RunOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sienna")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tan")))
        if True:
            if source0_.is_StackOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "royalblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "powderblue")))
        if True:
            if source0_.is_LogOp:
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "cornflowerblue")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lavender")))
        if True:
            d_0_opcode_ = source0_.opcode
            if ((d_0_opcode_) == (EVMConstants.default__.STOP)) or ((d_0_opcode_) == (EVMConstants.default__.REVERT)):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "brown")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lightsalmon")))
            elif (d_0_opcode_) == (EVMConstants.default__.RETURN):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "teal")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "greenyellow")))
            elif ((((d_0_opcode_) == (EVMConstants.default__.CALL)) or ((d_0_opcode_) == (EVMConstants.default__.CALLCODE))) or ((d_0_opcode_) == (EVMConstants.default__.DELEGATECALL))) or ((d_0_opcode_) == (EVMConstants.default__.STATICCALL)):
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
        return lambda: Instruction_Instruction(EVMOpcodes.ValidOpcode.default(), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Instruction(self) -> bool:
        return isinstance(self, Instruction_Instruction)
    def Size(self):
        return (1) + (_dafny.euclidian_division(len((self).arg), 2))

    def ToString(self):
        d_0_x_ = (self).arg
        if (((self).op).opcode) == (EVMConstants.default__.INVALID):
            return ((((self).op).Name()) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_0_x_)
        elif True:
            return (((self).op).Name()) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_0_x_) if (len(d_0_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))

    def Equiv(self, i):
        return (((self).op) == ((i).op)) and (((self).arg) == ((i).arg))

    def ToHTML(self):
        d_0_x_ = (self).arg
        d_1_cols_ = default__.Colours(self)
        d_2_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_3___v0_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_4_insText_ = (((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_1_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))) + (d_0_x_) if (((self).op).opcode) == (EVMConstants.default__.INVALID) else (((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\""))) + ((d_1_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " 0x"))) + (d_0_x_) if (len(d_0_x_)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))))
        return ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x"))) + (d_2_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":")))) + (d_4_insText_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " <BR ALIGN=\"LEFT\"/>\n")))

    def ToHTMLTable(self, entryPortTag, exitPortTag):
        d_0_cols_ = default__.Colours(self)
        d_1_formattedAddress_ = (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_2___v1_ in range(_dafny.euclidian_modulus(len(Hex.default__.NatToHex((self).address)), 2))])) + (Hex.default__.NatToHex((self).address))
        d_3_gasLine_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "&#9981; "))
        d_4_oplineTD_ = ((((((((((((((((((((((((((((((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"7\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: "))) + (EVMToolTips.default__.Gas(((self).op).opcode))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " \" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "target=\"_blank\" href=\"")))) + (EVMToolTips.default__.gasRefLine)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (d_3_gasLine_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" ")))) + (entryPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0x")))) + (d_1_formattedAddress_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " </TD>\n")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")))) + ((d_0_cols_)[1])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" align=\"left\" cellpadding=\"3\" ")))) + (exitPortTag)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " href=\"")))) + (EVMToolTips.default__.bytecodeRefLine)) + (Int.default__.NatToString((EVMToolTips.default__.ToolTip(((self).op).opcode))[1]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" target=\"_blank\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " tooltip=\"")))) + ((EVMToolTips.default__.ToolTip(((self).op).opcode))[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" ")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<FONT color=\"")))) + ((d_0_cols_)[0])) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\">")))) + (((self).op).Name())) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</FONT>")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>")))
        d_5_arglineTD_ = ((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TD width=\"1\" fixedsize=\"true\" align=\"left\">"))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  0x")))) + ((self).arg)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TD>"))) if (len((self).arg)) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_6_lineTR_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TR>"))) + (d_4_oplineTD_)) + (d_5_arglineTD_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TR>")))
        d_7_itemTable_ = ((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "<TABLE  border=\"0\" cellpadding=\"0\" cellborder=\"0\" CELLSPACING=\"1\">"))) + (d_6_lineTR_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "</TABLE>")))
        return d_7_itemTable_

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
        source0_ = (self).op
        if True:
            if source0_.is_ArithOp:
                d_0_pushes_ = source0_.pushes
                d_1_pops_ = source0_.pops
                if (pos_k) >= (1):
                    return MiscTypes.Either_Right((pos_k) + (1))
                elif True:
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Arithmetic operator with target 0"))))
        if True:
            if source0_.is_CompOp:
                d_2_pushes_ = source0_.pushes
                d_3_pops_ = source0_.pops
                if (pos_k) >= (1):
                    return MiscTypes.Either_Right(((pos_k) + (d_3_pops_)) - (d_2_pushes_))
                elif True:
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Comparison operator with target 0"))))
        if True:
            if source0_.is_BitwiseOp:
                d_4_pushes_ = source0_.pushes
                d_5_pops_ = source0_.pops
                if (pos_k) >= (1):
                    return MiscTypes.Either_Right(((pos_k) + (d_5_pops_)) - (d_4_pushes_))
                elif True:
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Bitwise operator with target 0"))))
        if True:
            if source0_.is_KeccakOp:
                d_6_pushes_ = source0_.pushes
                d_7_pops_ = source0_.pops
                if (pos_k) >= (1):
                    return MiscTypes.Either_Right((pos_k) + (1))
                elif True:
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Keccak operator with target 0"))))
        if True:
            if source0_.is_EnvOp:
                d_8_pushes_ = source0_.pushes
                d_9_pops_ = source0_.pops
                if ((d_8_pushes_) == (1)) and ((d_9_pops_) == (0)):
                    if (pos_k) == (0):
                        return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                    elif True:
                        return MiscTypes.Either_Right((pos_k) - (1))
                elif ((d_8_pushes_) == (1)) and ((d_9_pops_) == (1)):
                    if (pos_k) == (0):
                        return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Env operator with target 0"))))
                    elif True:
                        return MiscTypes.Either_Right(pos_k)
                elif True:
                    return MiscTypes.Either_Right(((pos_k) + (d_9_pops_)) - (d_8_pushes_))
        if True:
            if source0_.is_MemOp:
                d_10_pushes_ = source0_.pushes
                d_11_pops_ = source0_.pops
                if (d_10_pushes_) == (0):
                    return MiscTypes.Either_Right((pos_k) + (2))
                elif True:
                    if (pos_k) == (0):
                        return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Mem operator with target 0"))))
                    elif True:
                        return MiscTypes.Either_Right(pos_k)
        if True:
            if source0_.is_StorageOp:
                d_12_pushes_ = source0_.pushes
                d_13_pops_ = source0_.pops
                if (d_12_pushes_) == (0):
                    return MiscTypes.Either_Right((pos_k) + (2))
                elif True:
                    if (pos_k) == (0):
                        return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Storage operator with target 0"))))
                    elif True:
                        return MiscTypes.Either_Right(pos_k)
        if True:
            if source0_.is_JumpOp:
                d_14_opcode_ = source0_.opcode
                if (d_14_opcode_) == (EVMConstants.default__.JUMPDEST):
                    return MiscTypes.Either_Right(pos_k)
                elif ((EVMConstants.default__.JUMP) <= (d_14_opcode_)) and ((d_14_opcode_) <= (EVMConstants.default__.JUMPI)):
                    d_15_k_ = ((d_14_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                    return MiscTypes.Either_Right((pos_k) + (d_15_k_))
                elif True:
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Not implemented"))))
        if True:
            if source0_.is_RunOp:
                d_16_pushes_ = source0_.pushes
                d_17_pops_ = source0_.pops
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Run operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) - (1))
        if True:
            if source0_.is_StackOp:
                d_18_opcode_ = source0_.opcode
                if ((EVMConstants.default__.PUSH0) <= (d_18_opcode_)) and ((d_18_opcode_) <= (EVMConstants.default__.PUSH32)):
                    if (pos_k) == (0):
                        return MiscTypes.Either_Left(StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)))
                    elif True:
                        return MiscTypes.Either_Right((pos_k) - (1))
                elif ((EVMConstants.default__.DUP1) <= (d_18_opcode_)) and ((d_18_opcode_) <= (EVMConstants.default__.DUP16)):
                    return MiscTypes.Either_Right(((d_18_opcode_) - (EVMConstants.default__.DUP1) if (pos_k) == (0) else (pos_k) - (1)))
                elif ((EVMConstants.default__.SWAP1) <= (d_18_opcode_)) and ((d_18_opcode_) <= (EVMConstants.default__.SWAP16)):
                    d_19_k_ = ((d_18_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                    return MiscTypes.Either_Right((d_19_k_ if (pos_k) == (0) else (0 if (pos_k) == (d_19_k_) else pos_k)))
                elif True:
                    return MiscTypes.Either_Right((pos_k) + (1))
        if True:
            if source0_.is_LogOp:
                d_20_pushes_ = source0_.pushes
                d_21_pops_ = source0_.pops
                return MiscTypes.Either_Right((pos_k) + (d_21_pops_))
        if True:
            d_22_pushes_ = source0_.pushes
            d_23_pops_ = source0_.pops
            if (d_22_pushes_) == (0):
                return MiscTypes.Either_Right((pos_k) + (d_23_pops_))
            elif True:
                if (pos_k) == (0):
                    return MiscTypes.Either_Left(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "More than one predecessor. Sys operator with target 0"))))
                elif True:
                    return MiscTypes.Either_Right((pos_k) + (d_23_pops_))

    def NextState(self, s, jumpDests, exit):
        source0_ = (self).op
        if True:
            if source0_.is_ArithOp:
                d_0_pushes_ = source0_.pushes
                d_1_pops_ = source0_.pops
                if ((s).Size()) >= (d_1_pops_):
                    return (((s).PopN(d_1_pops_)).PushNRandom(d_0_pushes_)).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        if True:
            if source0_.is_CompOp:
                d_2_pushes_ = source0_.pushes
                d_3_pops_ = source0_.pops
                if ((s).Size()) >= (d_3_pops_):
                    return (((s).PopN(d_3_pops_)).PushNRandom(d_2_pushes_)).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        if True:
            if source0_.is_BitwiseOp:
                d_4_pushes_ = source0_.pushes
                d_5_pops_ = source0_.pops
                if ((s).Size()) >= (d_5_pops_):
                    return (((s).PopN(d_5_pops_)).PushNRandom(d_4_pushes_)).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        if True:
            if source0_.is_KeccakOp:
                d_6_pushes_ = source0_.pushes
                d_7_pops_ = source0_.pops
                if ((s).Size()) >= (2):
                    return (((s).PopN(2)).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack underflow")))
        if True:
            if source0_.is_EnvOp:
                d_8_pushes_ = source0_.pushes
                d_9_pops_ = source0_.pops
                if ((s).Size()) >= (d_9_pops_):
                    return (((s).PopN(d_9_pops_)).PushNRandom(d_8_pushes_)).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EnvOp error")))
        if True:
            if source0_.is_MemOp:
                d_10_pushes_ = source0_.pushes
                d_11_pops_ = source0_.pops
                if ((s).Size()) >= (d_11_pops_):
                    return (((s).PopN(d_11_pops_)).PushNRandom(d_10_pushes_)).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "MemOp error")))
        if True:
            if source0_.is_StorageOp:
                d_12_pushes_ = source0_.pushes
                d_13_pops_ = source0_.pops
                if ((s).Size()) >= (d_13_pops_):
                    return (((s).PopN(d_13_pops_)).PushNRandom(d_12_pushes_)).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Storage Op error")))
        if True:
            if source0_.is_JumpOp:
                d_14_opcode_ = source0_.opcode
                d_15_pushes_ = source0_.pushes
                d_16_pops_ = source0_.pops
                if (d_14_opcode_) == (EVMConstants.default__.JUMPDEST):
                    return (s).Skip(1)
                elif (d_14_opcode_) == (EVMConstants.default__.JUMP):
                    if ((s).Size()) >= (1):
                        source1_ = (s).Peek(0)
                        if True:
                            if source1_.is_Value:
                                d_17_v_ = source1_.v
                                return ((s).Pop()).Goto(d_17_v_)
                        if True:
                            return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Jump to Random() unknown PC error")))
                    elif True:
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMP/exit false or stack underflow")))
                elif (d_14_opcode_) == (EVMConstants.default__.JUMPI):
                    if ((s).Size()) >= (2):
                        source2_ = (s).Peek(0)
                        if True:
                            if source2_.is_Value:
                                d_18_v_ = source2_.v
                                if (exit) >= (1):
                                    return ((s).PopN(2)).Goto(d_18_v_)
                                elif True:
                                    return ((s).PopN(2)).Skip(1)
                        if True:
                            return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "JumpI to Random() error")))
                    elif True:
                        return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Cannot execute JUMPI/strack underflow")))
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RJUMPs not implemented")))
        if True:
            if source0_.is_RunOp:
                d_19_pushes_ = source0_.pushes
                d_20_pops_ = source0_.pops
                return ((s).Push(StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))).Skip(1)
        if True:
            if source0_.is_StackOp:
                d_21_opcode_ = source0_.opcode
                d_22_pushes_ = source0_.pushes
                d_23_pops_ = source0_.pops
                if ((d_21_opcode_) == (EVMConstants.default__.POP)) and (((s).Size()) >= (1)):
                    return ((s).Pop()).Skip(1)
                elif ((EVMConstants.default__.PUSH0) <= (d_21_opcode_)) and ((d_21_opcode_) <= (EVMConstants.default__.PUSH32)):
                    d_24_valToPush_ = (StackElement.StackElem_Value(default__.GetArgValuePush((self).arg)) if (default__.GetArgValuePush((self).arg)) in (jumpDests) else StackElement.StackElem_Random(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))))
                    return ((s).Push(d_24_valToPush_)).Skip((1) + ((d_21_opcode_) - (EVMConstants.default__.PUSH0)))
                elif (((EVMConstants.default__.DUP1) <= (d_21_opcode_)) and ((d_21_opcode_) <= (EVMConstants.default__.DUP16))) and (((s).Size()) >= (((d_21_opcode_) - (EVMConstants.default__.DUP1)) + (1))):
                    return ((s).Dup(((d_21_opcode_) - (EVMConstants.default__.DUP1)) + (1))).Skip(1)
                elif (((EVMConstants.default__.SWAP1) <= (d_21_opcode_)) and ((d_21_opcode_) <= (EVMConstants.default__.SWAP16))) and (((s).Size()) > (((d_21_opcode_) - (EVMConstants.default__.SWAP1)) + (1))):
                    return ((s).Swap(((d_21_opcode_) - (EVMConstants.default__.SWAP1)) + (1))).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stack Op error")))
        if True:
            if source0_.is_LogOp:
                d_25_pushes_ = source0_.pushes
                d_26_pops_ = source0_.pops
                if ((s).Size()) >= (d_26_pops_):
                    return ((s).PopN(d_26_pops_)).Skip(1)
                elif True:
                    return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "LogOp error")))
        if True:
            d_27_op_ = source0_.opcode
            d_28_pushes_ = source0_.pushes
            d_29_pops_ = source0_.pops
            if (((d_27_op_) == (EVMConstants.default__.INVALID)) or ((d_27_op_) == (EVMConstants.default__.STOP))) or ((d_27_op_) == (EVMConstants.default__.REVERT)):
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))
            elif ((s).Size()) >= (d_29_pops_):
                return (((s).PopN(d_29_pops_)).PushNRandom(d_28_pushes_)).Skip(1)
            elif True:
                return State.AState_Error(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "SysOp error")))

    def WPre(self, c):
        source0_ = (self).op
        if True:
            if source0_.is_ArithOp:
                d_0_pushes_ = source0_.pushes
                d_1_pops_ = source0_.pops
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda0_(d_3_pos_):
                        return (d_3_pos_) + (1)

                    d_2_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda0_)
                    return WeakPre.Cond_StCond(d_2_shiftByOne_, (c).TrackedVals())
        if True:
            if source0_.is_CompOp:
                d_4_pushes_ = source0_.pushes
                d_5_pops_ = source0_.pops
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda1_(d_7_pops_, d_8_pushes_):
                        def lambda2_(d_9_pos_):
                            return ((d_9_pos_) + (d_7_pops_)) - (d_8_pushes_)

                        return lambda2_

                    d_6_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda1_(d_5_pops_, d_4_pushes_))
                    return WeakPre.Cond_StCond(d_6_shiftBy_, (c).TrackedVals())
        if True:
            if source0_.is_BitwiseOp:
                d_10_pushes_ = source0_.pushes
                d_11_pops_ = source0_.pops
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda3_(d_13_pops_, d_14_pushes_):
                        def lambda4_(d_15_pos_):
                            return ((d_15_pos_) + (d_13_pops_)) - (d_14_pushes_)

                        return lambda4_

                    d_12_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda3_(d_11_pops_, d_10_pushes_))
                    return WeakPre.Cond_StCond(d_12_shiftBy_, (c).TrackedVals())
        if True:
            if source0_.is_KeccakOp:
                d_16_pushes_ = source0_.pushes
                d_17_pops_ = source0_.pops
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda5_(d_19_pos_):
                        return (d_19_pos_) + (1)

                    d_18_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda5_)
                    return WeakPre.Cond_StCond(d_18_shiftByOne_, (c).TrackedVals())
        if True:
            if source0_.is_EnvOp:
                d_20_pushes_ = source0_.pushes
                d_21_pops_ = source0_.pops
                if ((d_20_pushes_) == (1)) and ((d_21_pops_) == (0)):
                    if (0) in ((c).TrackedPos()):
                        return WeakPre.Cond_StFalse()
                    elif True:
                        def lambda6_(d_23_pos_):
                            return (d_23_pos_) - (1)

                        d_22_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda6_)
                        return WeakPre.Cond_StCond(d_22_shiftByOne_, (c).TrackedVals())
                elif ((d_20_pushes_) == (1)) and ((d_21_pops_) == (1)):
                    if (0) in ((c).TrackedPos()):
                        return WeakPre.Cond_StFalse()
                    elif True:
                        return c
                elif True:
                    def lambda7_(d_25_pops_, d_26_pushes_):
                        def lambda8_(d_27_pos_):
                            return ((d_27_pos_) + (d_25_pops_)) - (d_26_pushes_)

                        return lambda8_

                    d_24_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda7_(d_21_pops_, d_20_pushes_))
                    return WeakPre.Cond_StCond(d_24_shiftBy_, (c).TrackedVals())
        if True:
            if source0_.is_MemOp:
                d_28_pushes_ = source0_.pushes
                d_29_pops_ = source0_.pops
                if (d_28_pushes_) == (0):
                    def lambda9_(d_31_pos_):
                        return (d_31_pos_) + (2)

                    d_30_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda9_)
                    return WeakPre.Cond_StCond(d_30_shiftByTwo_, (c).TrackedVals())
                elif True:
                    if (0) in ((c).TrackedPos()):
                        return WeakPre.Cond_StFalse()
                    elif True:
                        return c
        if True:
            if source0_.is_StorageOp:
                d_32_pushes_ = source0_.pushes
                d_33_pops_ = source0_.pops
                if (d_32_pushes_) == (0):
                    def lambda10_(d_35_pos_):
                        return (d_35_pos_) + (2)

                    d_34_shiftByTwo_ = MiscTypes.default__.Map((c).TrackedPos(), lambda10_)
                    return WeakPre.Cond_StCond(d_34_shiftByTwo_, (c).TrackedVals())
                elif True:
                    if (0) in ((c).TrackedPos()):
                        return WeakPre.Cond_StFalse()
                    elif True:
                        return c
        if True:
            if source0_.is_JumpOp:
                d_36_opcode_ = source0_.opcode
                if (d_36_opcode_) == (EVMConstants.default__.JUMPDEST):
                    return c
                elif ((EVMConstants.default__.JUMP) <= (d_36_opcode_)) and ((d_36_opcode_) <= (EVMConstants.default__.JUMPI)):
                    d_37_k_ = ((d_36_opcode_) - (EVMConstants.default__.JUMP)) + (1)
                    def lambda11_(d_39_k_):
                        def lambda12_(d_40_pos_):
                            return (d_40_pos_) + (d_39_k_)

                        return lambda12_

                    d_38_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda11_(d_37_k_))
                    return WeakPre.Cond_StCond(d_38_shiftBy_, (c).TrackedVals())
                elif True:
                    return WeakPre.Cond_StFalse()
        if True:
            if source0_.is_RunOp:
                d_41_opcode_ = source0_.opcode
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda13_(d_43_pos_):
                        return (d_43_pos_) - (1)

                    d_42_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda13_)
                    return WeakPre.Cond_StCond(d_42_shiftByOne_, (c).TrackedVals())
        if True:
            if source0_.is_StackOp:
                d_44_opcode_ = source0_.opcode
                if ((EVMConstants.default__.PUSH0) <= (d_44_opcode_)) and ((d_44_opcode_) <= (EVMConstants.default__.PUSH32)):
                    source1_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                    if True:
                        if source1_.is_None:
                            def lambda14_(d_46_pos_):
                                return (d_46_pos_) - (1)

                            d_45_shiftByMinusOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda14_)
                            return WeakPre.Cond_StCond(d_45_shiftByMinusOne_, (c).TrackedVals())
                    if True:
                        d_47_i_ = source1_.v
                        d_48_argVal_ = Hex.default__.HexToU256((_dafny.SeqWithoutIsStrInference([_dafny.CodePoint('0') for d_49___v142_ in range((64) - (len((self).arg)))])) + ((self).arg))
                        if ((c).TrackedValAt(d_47_i_)) == ((d_48_argVal_).Extract()):
                            d_50_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_47_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_47_i_) + (1)::]))
                            if (len(d_50_filtered_)) == (0):
                                return WeakPre.Cond_StTrue()
                            elif True:
                                def lambda15_(d_52_pos_):
                                    return (d_52_pos_) - (1)

                                d_51_shiftByMinusOne_ = MiscTypes.default__.Map(d_50_filtered_, lambda15_)
                                return WeakPre.Cond_StCond(d_51_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_47_i_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_47_i_) + (1)::])))
                        elif True:
                            return WeakPre.Cond_StFalse()
                elif ((EVMConstants.default__.DUP1) <= (d_44_opcode_)) and ((d_44_opcode_) <= (EVMConstants.default__.DUP16)):
                    source2_ = MiscTypes.default__.Find((c).TrackedPos(), 0)
                    if True:
                        if source2_.is_None:
                            def lambda16_(d_54_pos_):
                                return (d_54_pos_) - (1)

                            d_53_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda16_)
                            return WeakPre.Cond_StCond(d_53_shiftByMinusOneButZero_, (c).TrackedVals())
                    if True:
                        d_55_index0_ = source2_.v
                        source3_ = MiscTypes.default__.Find((c).TrackedPos(), ((d_44_opcode_) - (EVMConstants.default__.DUP1)) + (1))
                        if True:
                            if source3_.is_Some:
                                d_56_index_ = source3_.v
                                if ((c).TrackedValAt(d_55_index0_)) == ((c).TrackedValAt(d_56_index_)):
                                    d_57_filtered_ = (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[:d_55_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedPos())[(d_55_index0_) + (1)::]))
                                    def lambda17_(d_59_pos_):
                                        return (d_59_pos_) - (1)

                                    d_58_shiftByMinusOne_ = MiscTypes.default__.Map(d_57_filtered_, lambda17_)
                                    return WeakPre.Cond_StCond(d_58_shiftByMinusOne_, (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[:d_55_index0_:])) + (_dafny.SeqWithoutIsStrInference(((c).TrackedVals())[(d_55_index0_) + (1)::])))
                                elif True:
                                    return WeakPre.Cond_StFalse()
                        if True:
                            def lambda18_(d_61_opcode_):
                                def lambda19_(d_62_pos_):
                                    return ((d_61_opcode_) - (EVMConstants.default__.DUP1) if (d_62_pos_) == (0) else (d_62_pos_) - (1))

                                return lambda19_

                            d_60_shiftByMinusOneButZero_ = MiscTypes.default__.Map((c).TrackedPos(), lambda18_(d_44_opcode_))
                            return WeakPre.Cond_StCond(d_60_shiftByMinusOneButZero_, (c).TrackedVals())
                elif ((EVMConstants.default__.SWAP1) <= (d_44_opcode_)) and ((d_44_opcode_) <= (EVMConstants.default__.SWAP16)):
                    d_63_k_ = ((d_44_opcode_) - (EVMConstants.default__.SWAP1)) + (1)
                    def lambda20_(d_65_k_):
                        def lambda21_(d_66_pos_):
                            return (d_65_k_ if (d_66_pos_) == (0) else (0 if (d_66_pos_) == (d_65_k_) else d_66_pos_))

                        return lambda21_

                    d_64_swapZeroAndk_ = MiscTypes.default__.Map((c).TrackedPos(), lambda20_(d_63_k_))
                    return WeakPre.Cond_StCond(d_64_swapZeroAndk_, (c).TrackedVals())
                elif True:
                    def lambda22_(d_68_i_):
                        return (d_68_i_) + (1)

                    d_67_shiftByOne_ = MiscTypes.default__.Map((c).TrackedPos(), lambda22_)
                    return WeakPre.Cond_StCond(d_67_shiftByOne_, (c).TrackedVals())
        if True:
            if source0_.is_LogOp:
                d_69_opcode_ = source0_.opcode
                d_70_pushes_ = source0_.pushes
                d_71_pops_ = source0_.pops
                def lambda23_(d_73_pops_):
                    def lambda24_(d_74_pos_):
                        return (d_74_pos_) + (d_73_pops_)

                    return lambda24_

                d_72_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda23_(d_71_pops_))
                return WeakPre.Cond_StCond(d_72_shiftBy_, (c).TrackedVals())
        if True:
            d_75_opcode_ = source0_.opcode
            d_76_pushes_ = source0_.pushes
            d_77_pops_ = source0_.pops
            if (d_76_pushes_) == (0):
                def lambda25_(d_79_pops_):
                    def lambda26_(d_80_pos_):
                        return (d_80_pos_) + (d_79_pops_)

                    return lambda26_

                d_78_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda25_(d_77_pops_))
                return WeakPre.Cond_StCond(d_78_shiftBy_, (c).TrackedVals())
            elif True:
                if (0) in ((c).TrackedPos()):
                    return WeakPre.Cond_StFalse()
                elif True:
                    def lambda27_(d_82_pops_):
                        def lambda28_(d_83_pos_):
                            return (d_83_pos_) + (d_82_pops_)

                        return lambda28_

                    d_81_shiftBy_ = MiscTypes.default__.Map((c).TrackedPos(), lambda27_(d_77_pops_))
                    return WeakPre.Cond_StCond(d_81_shiftBy_, (c).TrackedVals())


class Instruction_Instruction(Instruction, NamedTuple('Instruction', [('op', Any), ('arg', Any), ('address', Any)])):
    def __dafnystr__(self) -> str:
        return f'Instructions.Instruction.Instruction({_dafny.string_of(self.op)}, {self.arg.VerbatimString(True)}, {_dafny.string_of(self.address)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Instruction_Instruction) and self.op == __o.op and self.arg == __o.arg and self.address == __o.address
    def __hash__(self) -> int:
        return super().__hash__()

