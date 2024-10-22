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

# Module: EVMToolTips

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def ToolTip(op):
        source0_ = op
        if True:
            if (source0_) == (0):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Halts the machine without return output data")), 32)
        if True:
            if (source0_) == (1):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer addition modulo TWO_256")), 40)
        if True:
            if (source0_) == (2):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer multiplication modulo TWO_256")), 61)
        if True:
            if (source0_) == (3):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer subtraction modulo TWO_256")), 81)
        if True:
            if (source0_) == (4):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer division modulo TWO_256. Div by 0 yields 0")), 154)
        if True:
            if (source0_) == (5):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Signed integer division modulo TWO_256. Div by 0 yields 0")), 173)
        if True:
            if (source0_) == (6):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned modulo remainder")), 195)
        if True:
            if (source0_) == (7):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Signed modulo remainder")), 211)
        if True:
            if (source0_) == (8):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer addition modulo")), 230)
        if True:
            if (source0_) == (9):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer multiplication modulo")), 250)
        if True:
            if (source0_) == (10):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exponential")), 272)
        if True:
            if (source0_) == (11):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Extend length of two's complement signed integer")), 291)
        if True:
            if (source0_) == (16):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned Less than")), 314)
        if True:
            if (source0_) == (17):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned Greater than")), 336)
        if True:
            if (source0_) == (18):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Signed less than")), 358)
        if True:
            if (source0_) == (19):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Signed greater than")), 380)
        if True:
            if (source0_) == (20):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "equal")), 402)
        if True:
            if (source0_) == (21):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Is equal to zero")), 424)
        if True:
            if (source0_) == (22):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise AND")), 445)
        if True:
            if (source0_) == (23):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise OR")), 464)
        if True:
            if (source0_) == (24):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise XOR")), 484)
        if True:
            if (source0_) == (25):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise NOT")), 504)
        if True:
            if (source0_) == (26):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Extract a byte from a word.")), 522)
        if True:
            if (source0_) == (27):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Left shift")), 541)
        if True:
            if (source0_) == (28):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Right shift")), 560)
        if True:
            if (source0_) == (29):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Arithmetic (signed) right shift operation")), 579)
        if True:
            if (source0_) == (32):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Keccak 256 hash")), 598)
        if True:
            if (source0_) == (48):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Address of current executing account")), 640)
        if True:
            if (source0_) == (49):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Balance of a given account")), 655)
        if True:
            if (source0_) == (50):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Originator's address")), 676)
        if True:
            if (source0_) == (51):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Caller address")), 692)
        if True:
            if (source0_) == (52):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Value deposited by function call")), 707)
        if True:
            if (source0_) == (53):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Input data for this call")), 723)
        if True:
            if (source0_) == (54):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of the input data")), 742)
        if True:
            if (source0_) == (55):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Copy input data to memory")), 759)
        if True:
            if (source0_) == (56):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of the code of this contract")), 783)
        if True:
            if (source0_) == (57):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Copy the executing code to memory")), 799)
        if True:
            if (source0_) == (58):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Gas price in current block")), 824)
        if True:
            if (source0_) == (59):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of the calling account's code")), 839)
        if True:
            if (source0_) == (60):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Copy account's code to memory")), 866)
        if True:
            if (source0_) == (61):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of return data from previous call")), 920)
        if True:
            if (source0_) == (62):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Copy return data from previous call to memory")), 937)
        if True:
            if (source0_) == (63):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Hash of account's code")), 895)
        if True:
            if (source0_) == (64):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Hash of current block")), 626)
        if True:
            if (source0_) == (65):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's beneficiay address")), 970)
        if True:
            if (source0_) == (66):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's timestamp")), 985)
        if True:
            if (source0_) == (67):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's number")), 1000)
        if True:
            if (source0_) == (68):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's difficulty")), 1015)
        if True:
            if (source0_) == (69):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's gas limit")), 1030)
        if True:
            if (source0_) == (70):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Chain ID")), 1045)
        if True:
            if (source0_) == (71):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Balance of currently executing account")), 1060)
        if True:
            if (source0_) == (72):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Base fee for the currently executing block")), 1080)
        if True:
            if (source0_) == (80):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Pop top of stack")), 1097)
        if True:
            if (source0_) == (81):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Read a word from memory")), 1133)
        if True:
            if (source0_) == (82):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Store a word to memory")), 1165)
        if True:
            if (source0_) == (83):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Store a byte to memory")), 1195)
        if True:
            if (source0_) == (84):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Read a word from storage")), 1214)
        if True:
            if (source0_) == (85):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Store a word to storage")), 1233)
        if True:
            if (source0_) == (86):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Uncoditional Jump")), 1255)
        if True:
            if (source0_) == (87):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Conditional Jump")), 1277)
        if True:
            if (source0_) == (92):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Static relative jump using a given offset")), 1343)
        if True:
            if (source0_) == (93):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Conditional Static relative jump using a given offset")), 1363)
        if True:
            if (source0_) == (94):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Relative jump via a jump table of one or more relative offsets")), 1392)
        if True:
            if (source0_) == (88):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Value of program counter")), 1302)
        if True:
            if (source0_) == (89):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of allocated memory")), 1113)
        if True:
            if (source0_) == (90):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Amount of available gas")), 1318)
        if True:
            if (source0_) == (91):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "A valid destination for a jump")), 1334)
        if True:
            if (source0_) == (95):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 0 on stack")), 1428)
        if True:
            if (source0_) == (96):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 1 byte")), 1479)
        if True:
            if (source0_) == (97):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 2 bytes")), 1486)
        if True:
            if (source0_) == (98):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 3 bytes")), 1493)
        if True:
            if (source0_) == (99):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 4 bytes")), 1500)
        if True:
            if (source0_) == (100):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 5 bytes")), 1507)
        if True:
            if (source0_) == (101):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 6 bytes")), 1514)
        if True:
            if (source0_) == (102):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 7 bytes")), 1521)
        if True:
            if (source0_) == (103):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 8 bytes")), 1528)
        if True:
            if (source0_) == (104):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 9 bytes")), 1535)
        if True:
            if (source0_) == (105):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 10 bytes")), 1535)
        if True:
            if (source0_) == (106):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 11 bytes")), 1535)
        if True:
            if (source0_) == (107):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 12 bytes")), 1535)
        if True:
            if (source0_) == (108):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 13 bytes")), 1535)
        if True:
            if (source0_) == (109):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 14 bytes")), 1535)
        if True:
            if (source0_) == (110):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 15 bytes")), 1535)
        if True:
            if (source0_) == (111):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 16 bytes")), 1535)
        if True:
            if (source0_) == (112):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 17 bytes")), 1535)
        if True:
            if (source0_) == (113):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 18 bytes")), 1535)
        if True:
            if (source0_) == (114):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 19 bytes")), 1535)
        if True:
            if (source0_) == (115):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 20 bytes")), 1535)
        if True:
            if (source0_) == (116):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 21 bytes")), 1535)
        if True:
            if (source0_) == (117):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 22 bytes")), 1535)
        if True:
            if (source0_) == (118):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 23 bytes")), 1535)
        if True:
            if (source0_) == (119):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 24 bytes")), 1535)
        if True:
            if (source0_) == (120):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 25 bytes")), 1535)
        if True:
            if (source0_) == (121):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 26 bytes")), 1535)
        if True:
            if (source0_) == (122):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 27 bytes")), 1535)
        if True:
            if (source0_) == (123):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 28 bytes")), 1535)
        if True:
            if (source0_) == (124):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 29 bytes")), 1535)
        if True:
            if (source0_) == (125):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 30 bytes")), 1535)
        if True:
            if (source0_) == (126):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 31 bytes")), 1535)
        if True:
            if (source0_) == (127):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 32 bytes")), 1535)
        if True:
            if (source0_) == (128):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 1st element on top of the stack")), 1568)
        if True:
            if (source0_) == (129):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 2nd element on top of the stack")), 1568)
        if True:
            if (source0_) == (130):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 3rd element on top of the stack")), 1568)
        if True:
            if (source0_) == (131):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 4-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (132):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 5-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (133):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 6-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (134):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 7-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (135):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 8-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (136):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 9-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (137):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 10-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (138):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 11-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (139):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 12-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (140):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 13-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (141):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 14-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (142):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 15-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (143):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 16-th element on top of the stack")), 1568)
        if True:
            if (source0_) == (144):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 2nd element of the stack")), 1577)
        if True:
            if (source0_) == (145):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 3rd element of the stack")), 1577)
        if True:
            if (source0_) == (146):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 4-th element of the stack")), 1577)
        if True:
            if (source0_) == (147):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 5-th element of the stack")), 1577)
        if True:
            if (source0_) == (148):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 6-th element of the stack")), 1577)
        if True:
            if (source0_) == (149):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 7-th element of the stack")), 1577)
        if True:
            if (source0_) == (150):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 8-th element of the stack")), 1577)
        if True:
            if (source0_) == (151):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 9-th element of the stack")), 1577)
        if True:
            if (source0_) == (152):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 10-th element of the stack")), 1577)
        if True:
            if (source0_) == (153):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 11-th element of the stack")), 1577)
        if True:
            if (source0_) == (154):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 12-th element of the stack")), 1577)
        if True:
            if (source0_) == (155):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 13-th element of the stack")), 1577)
        if True:
            if (source0_) == (156):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 14-th element of the stack")), 1577)
        if True:
            if (source0_) == (157):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 15-th element of the stack")), 1577)
        if True:
            if (source0_) == (158):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 16-th element of the stack")), 1577)
        if True:
            if (source0_) == (159):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 17-th element of the stack")), 1577)
        if True:
            if (source0_) == (160):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 0 topics")), 1600)
        if True:
            if (source0_) == (161):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 1 topics")), 1600)
        if True:
            if (source0_) == (162):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 2 topics")), 1600)
        if True:
            if (source0_) == (163):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 3 topics")), 1600)
        if True:
            if (source0_) == (164):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 4 topics")), 1600)
        if True:
            if (source0_) == (240):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Create a new account with associated code")), 1629)
        if True:
            if (source0_) == (241):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Message-call into an account")), 1674)
        if True:
            if (source0_) == (242):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Message-call into this account with another account's code")), 1711)
        if True:
            if (source0_) == (243):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Halt execution and return data")), 1742)
        if True:
            if (source0_) == (244):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Message-call into this account with an alternative account's code")), 1764)
        if True:
            if (source0_) == (245):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Create a new account with associated code")), 1799)
        if True:
            if (source0_) == (250):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Static Message-call into an account")), 1844)
        if True:
            if (source0_) == (253):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Revert execution and return data")), 1874)
        if True:
            if (source0_) == (255):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Delete this account")), 1896)
        if True:
            if (source0_) == (254):
                return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Equivalent to STOP")), 32)
        if True:
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "N/A")), 0)

    @staticmethod
    def Gas(op):
        source0_ = op
        if True:
            if (source0_) == (0):
                return Int.default__.NatToString(default__.G__ZERO)
        if True:
            if (source0_) == (1):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (2):
                return Int.default__.NatToString(default__.G__LOW)
        if True:
            if (source0_) == (3):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (4):
                return Int.default__.NatToString(default__.G__LOW)
        if True:
            if (source0_) == (5):
                return Int.default__.NatToString(default__.G__LOW)
        if True:
            if (source0_) == (6):
                return Int.default__.NatToString(default__.G__LOW)
        if True:
            if (source0_) == (7):
                return Int.default__.NatToString(default__.G__LOW)
        if True:
            if (source0_) == (8):
                return Int.default__.NatToString(default__.G__MID)
        if True:
            if (source0_) == (9):
                return Int.default__.NatToString(default__.G__MID)
        if True:
            if (source0_) == (10):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (11):
                return Int.default__.NatToString(default__.G__LOW)
        if True:
            if (source0_) == (16):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (17):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (18):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (19):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (20):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (21):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (22):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (23):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (24):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (25):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (26):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (27):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (28):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (29):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (32):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (48):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (50):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (51):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (52):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (53):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (54):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (55):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (56):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (57):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (58):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (59):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (60):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (61):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (62):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (63):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (64):
                return Int.default__.NatToString(default__.G__BLOCKHASH)
        if True:
            if (source0_) == (65):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (66):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (67):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (68):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (69):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (70):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (71):
                return Int.default__.NatToString(default__.G__LOW)
        if True:
            if (source0_) == (72):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (80):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (81):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (82):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (83):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (84):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (85):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (86):
                return Int.default__.NatToString(default__.G__MID)
        if True:
            if (source0_) == (87):
                return Int.default__.NatToString(default__.G__HIGH)
        if True:
            if (source0_) == (88):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (89):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (90):
                return Int.default__.NatToString(default__.G__BASE)
        if True:
            if (source0_) == (91):
                return Int.default__.NatToString(default__.G__JUMPDEST)
        if True:
            if (source0_) == (95):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (96):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (97):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (98):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (99):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (100):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (101):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (102):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (103):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (104):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (105):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (106):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (107):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (108):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (109):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (110):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (111):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (112):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (113):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (114):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (115):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (116):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (117):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (118):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (119):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (120):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (121):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (122):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (123):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (124):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (125):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (126):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (127):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (128):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (129):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (130):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (131):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (132):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (133):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (134):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (135):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (136):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (137):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (138):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (139):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (140):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (141):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (142):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (143):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (144):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (145):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (146):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (147):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (148):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (149):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (150):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (151):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (152):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (153):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (154):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (155):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (156):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (157):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (158):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (159):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            if (source0_) == (160):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (161):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (162):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (163):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (164):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (240):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (241):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (242):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (243):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (244):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (245):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (250):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (253):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (255):
                return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        if True:
            if (source0_) == (254):
                return Int.default__.NatToString(default__.G__VERYLOW)
        if True:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unknown opcode"))

    @_dafny.classproperty
    def G__ZERO(instance):
        return 0
    @_dafny.classproperty
    def G__VERYLOW(instance):
        return 3
    @_dafny.classproperty
    def G__LOW(instance):
        return 5
    @_dafny.classproperty
    def G__MID(instance):
        return 8
    @_dafny.classproperty
    def G__BASE(instance):
        return 2
    @_dafny.classproperty
    def G__BLOCKHASH(instance):
        return 20
    @_dafny.classproperty
    def G__HIGH(instance):
        return 10
    @_dafny.classproperty
    def G__JUMPDEST(instance):
        return 1
    @_dafny.classproperty
    def bytecodeRefLine(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "https://github.com/Consensys/evm-dafny/blob/60bce44ee75978a4c97b9eab8e03424c9c233bbd/src/dafny/bytecode.dfy#L"))
    @_dafny.classproperty
    def gasRefLine(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "https://github.com/Consensys/evm-dafny/blob/60bce44ee75978a4c97b9eab8e03424c9c233bbd/src/dafny/evm.dfy#L103"))
    @_dafny.classproperty
    def G__WARMACCESS(instance):
        return 100
    @_dafny.classproperty
    def G__COLDACCOUNTACCESS(instance):
        return 2600
    @_dafny.classproperty
    def G__COLDSLOAD(instance):
        return 2100
    @_dafny.classproperty
    def G__SSET(instance):
        return 20000
    @_dafny.classproperty
    def G__SRESET(instance):
        return 2900
    @_dafny.classproperty
    def R__SCLEAR(instance):
        return 15000
    @_dafny.classproperty
    def R__SELFDESTRUCT(instance):
        return 24000
    @_dafny.classproperty
    def G__SELFDESTRUCT(instance):
        return 5000
    @_dafny.classproperty
    def G__CREATE(instance):
        return 32000
    @_dafny.classproperty
    def G__CODEDEPOSIT(instance):
        return 200
    @_dafny.classproperty
    def G__CALLVALUE(instance):
        return 9000
    @_dafny.classproperty
    def G__CALLSTIPEND(instance):
        return 2300
    @_dafny.classproperty
    def G__NEWACCOUNT(instance):
        return 25000
    @_dafny.classproperty
    def G__EXP(instance):
        return 10
    @_dafny.classproperty
    def G__EXPBYTE(instance):
        return 50
    @_dafny.classproperty
    def G__MEMORY(instance):
        return 3
    @_dafny.classproperty
    def G__TXCREATE(instance):
        return 32000
    @_dafny.classproperty
    def G__TXDATAZERO(instance):
        return 4
    @_dafny.classproperty
    def G__TXDATANONZERO(instance):
        return 16
    @_dafny.classproperty
    def G__TRANSACTION(instance):
        return 21000
    @_dafny.classproperty
    def G__LOG(instance):
        return 375
    @_dafny.classproperty
    def G__LOGDATA(instance):
        return 8
    @_dafny.classproperty
    def G__LOGTOPIC(instance):
        return 375
    @_dafny.classproperty
    def G__KECCAK256(instance):
        return 30
    @_dafny.classproperty
    def G__KECCAK256WORD(instance):
        return 6
    @_dafny.classproperty
    def G__COPY(instance):
        return 3
