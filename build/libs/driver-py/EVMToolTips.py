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

# Module: EVMToolTips

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def ToolTip(op):
        if (op) == (0):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Halts the machine without return output data")), 32)
        elif (op) == (1):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer addition modulo TWO_256")), 40)
        elif (op) == (2):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer multiplication modulo TWO_256")), 61)
        elif (op) == (3):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer subtraction modulo TWO_256")), 81)
        elif (op) == (4):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer division modulo TWO_256. Div by 0 yields 0")), 154)
        elif (op) == (5):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Signed integer division modulo TWO_256. Div by 0 yields 0")), 173)
        elif (op) == (6):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned modulo remainder")), 195)
        elif (op) == (7):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Signed modulo remainder")), 211)
        elif (op) == (8):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer addition modulo")), 230)
        elif (op) == (9):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned integer multiplication modulo")), 250)
        elif (op) == (10):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Exponential")), 272)
        elif (op) == (11):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Extend length of two's complement signed integer")), 291)
        elif (op) == (16):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned Less than")), 314)
        elif (op) == (17):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsigned Greater than")), 336)
        elif (op) == (18):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Signed less than")), 358)
        elif (op) == (19):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Signed greater than")), 380)
        elif (op) == (20):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "equal")), 402)
        elif (op) == (21):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Is equal to zero")), 424)
        elif (op) == (22):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise AND")), 445)
        elif (op) == (23):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise OR")), 464)
        elif (op) == (24):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise XOR")), 484)
        elif (op) == (25):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Bitwise NOT")), 504)
        elif (op) == (26):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Extract a byte from a word.")), 522)
        elif (op) == (27):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Left shift")), 541)
        elif (op) == (28):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Right shift")), 560)
        elif (op) == (29):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Arithmetic (signed) right shift operation")), 579)
        elif (op) == (32):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Keccak 256 hash")), 598)
        elif (op) == (48):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Address of current executing account")), 640)
        elif (op) == (49):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Balance of a given account")), 655)
        elif (op) == (50):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Originator's address")), 676)
        elif (op) == (51):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Caller address")), 692)
        elif (op) == (52):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Value deposited by function call")), 707)
        elif (op) == (53):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Input data for this call")), 723)
        elif (op) == (54):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of the input data")), 742)
        elif (op) == (55):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Copy input data to memory")), 759)
        elif (op) == (56):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of the code of this contract")), 783)
        elif (op) == (57):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Copy the executing code to memory")), 799)
        elif (op) == (58):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Gas price in current block")), 824)
        elif (op) == (59):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of the calling account's code")), 839)
        elif (op) == (60):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Copy account's code to memory")), 866)
        elif (op) == (61):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of return data from previous call")), 920)
        elif (op) == (62):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Copy return data from previous call to memory")), 937)
        elif (op) == (63):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Hash of account's code")), 895)
        elif (op) == (64):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Hash of current block")), 626)
        elif (op) == (65):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's beneficiay address")), 970)
        elif (op) == (66):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's timestamp")), 985)
        elif (op) == (67):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's number")), 1000)
        elif (op) == (68):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's difficulty")), 1015)
        elif (op) == (69):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Current block's gas limit")), 1030)
        elif (op) == (70):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Chain ID")), 1045)
        elif (op) == (71):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Balance of currently executing account")), 1060)
        elif (op) == (72):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Base fee for the currently executing block")), 1080)
        elif (op) == (80):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Pop top of stack")), 1097)
        elif (op) == (81):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Read a word from memory")), 1133)
        elif (op) == (82):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Store a word to memory")), 1165)
        elif (op) == (83):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Store a byte to memory")), 1195)
        elif (op) == (84):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Read a word from storage")), 1214)
        elif (op) == (85):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Store a word to storage")), 1233)
        elif (op) == (86):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Uncoditional Jump")), 1255)
        elif (op) == (87):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Conditional Jump")), 1277)
        elif (op) == (92):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Static relative jump using a given offset")), 1343)
        elif (op) == (93):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Conditional Static relative jump using a given offset")), 1363)
        elif (op) == (94):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Relative jump via a jump table of one or more relative offsets")), 1392)
        elif (op) == (88):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Value of program counter")), 1302)
        elif (op) == (89):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Size of allocated memory")), 1113)
        elif (op) == (90):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Amount of available gas")), 1318)
        elif (op) == (91):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "A valid destination for a jump")), 1334)
        elif (op) == (95):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 0 on stack")), 1428)
        elif (op) == (96):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 1 byte")), 1479)
        elif (op) == (97):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 2 bytes")), 1486)
        elif (op) == (98):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 3 bytes")), 1493)
        elif (op) == (99):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 4 bytes")), 1500)
        elif (op) == (100):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 5 bytes")), 1507)
        elif (op) == (101):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 6 bytes")), 1514)
        elif (op) == (102):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 7 bytes")), 1521)
        elif (op) == (103):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 8 bytes")), 1528)
        elif (op) == (104):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 9 bytes")), 1535)
        elif (op) == (105):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 10 bytes")), 1535)
        elif (op) == (106):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 11 bytes")), 1535)
        elif (op) == (107):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 12 bytes")), 1535)
        elif (op) == (108):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 13 bytes")), 1535)
        elif (op) == (109):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 14 bytes")), 1535)
        elif (op) == (110):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 15 bytes")), 1535)
        elif (op) == (111):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 16 bytes")), 1535)
        elif (op) == (112):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 17 bytes")), 1535)
        elif (op) == (113):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 18 bytes")), 1535)
        elif (op) == (114):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 19 bytes")), 1535)
        elif (op) == (115):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 20 bytes")), 1535)
        elif (op) == (116):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 21 bytes")), 1535)
        elif (op) == (117):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 22 bytes")), 1535)
        elif (op) == (118):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 23 bytes")), 1535)
        elif (op) == (119):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 24 bytes")), 1535)
        elif (op) == (120):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 25 bytes")), 1535)
        elif (op) == (121):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 26 bytes")), 1535)
        elif (op) == (122):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 27 bytes")), 1535)
        elif (op) == (123):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 28 bytes")), 1535)
        elif (op) == (124):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 29 bytes")), 1535)
        elif (op) == (125):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 30 bytes")), 1535)
        elif (op) == (126):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 31 bytes")), 1535)
        elif (op) == (127):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Push 32 bytes")), 1535)
        elif (op) == (128):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 1st element on top of the stack")), 1568)
        elif (op) == (129):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 2nd element on top of the stack")), 1568)
        elif (op) == (130):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 3rd element on top of the stack")), 1568)
        elif (op) == (131):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 4-th element on top of the stack")), 1568)
        elif (op) == (132):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 5-th element on top of the stack")), 1568)
        elif (op) == (133):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 6-th element on top of the stack")), 1568)
        elif (op) == (134):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 7-th element on top of the stack")), 1568)
        elif (op) == (135):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 8-th element on top of the stack")), 1568)
        elif (op) == (136):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 9-th element on top of the stack")), 1568)
        elif (op) == (137):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 10-th element on top of the stack")), 1568)
        elif (op) == (138):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 11-th element on top of the stack")), 1568)
        elif (op) == (139):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 12-th element on top of the stack")), 1568)
        elif (op) == (140):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 13-th element on top of the stack")), 1568)
        elif (op) == (141):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 14-th element on top of the stack")), 1568)
        elif (op) == (142):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 15-th element on top of the stack")), 1568)
        elif (op) == (143):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Duplicate 16-th element on top of the stack")), 1568)
        elif (op) == (144):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 2nd element of the stack")), 1577)
        elif (op) == (145):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 3rd element of the stack")), 1577)
        elif (op) == (146):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 4-th, element of the stack")), 1577)
        elif (op) == (147):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 5-th element of the stack")), 1577)
        elif (op) == (148):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 6-th element of the stack")), 1577)
        elif (op) == (149):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 7-th element of the stack")), 1577)
        elif (op) == (150):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 8-th element of the stack")), 1577)
        elif (op) == (151):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 9-th element of the stack")), 1577)
        elif (op) == (152):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 10-th element of the stack")), 1577)
        elif (op) == (153):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 11-th element of the stack")), 1577)
        elif (op) == (154):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 12-th element of the stack")), 1577)
        elif (op) == (155):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 13-th element of the stack")), 1577)
        elif (op) == (156):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 14-th element of the stack")), 1577)
        elif (op) == (157):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 15-th element of the stack")), 1577)
        elif (op) == (158):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 16-th element of the stack")), 1577)
        elif (op) == (159):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Swap top and 17-th element of the stack")), 1577)
        elif (op) == (160):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 0 topics")), 1600)
        elif (op) == (161):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 1 topics")), 1600)
        elif (op) == (162):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 2 topics")), 1600)
        elif (op) == (163):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 3 topics")), 1600)
        elif (op) == (164):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Append log with 4 topics")), 1600)
        elif (op) == (240):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Create a new account with associated code")), 1629)
        elif (op) == (241):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Message-call into an account")), 1674)
        elif (op) == (242):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Message-call into this account with another account's code")), 1711)
        elif (op) == (243):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Halt execution and return data")), 1742)
        elif (op) == (244):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Message-call into this account with an alternative account's code")), 1764)
        elif (op) == (245):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Create a new account with associated code")), 1799)
        elif (op) == (250):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Static Message-call into an account")), 1844)
        elif (op) == (253):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Revert execution and return data")), 1874)
        elif (op) == (255):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Delete this account")), 1896)
        elif (op) == (254):
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Equivalent to STOP")), 32)
        elif True:
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "N/A")), 0)

    @staticmethod
    def Gas(op):
        if (op) == (0):
            return Int.default__.NatToString(default__.G__ZERO)
        elif (op) == (1):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (2):
            return Int.default__.NatToString(default__.G__LOW)
        elif (op) == (3):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (4):
            return Int.default__.NatToString(default__.G__LOW)
        elif (op) == (5):
            return Int.default__.NatToString(default__.G__LOW)
        elif (op) == (6):
            return Int.default__.NatToString(default__.G__LOW)
        elif (op) == (7):
            return Int.default__.NatToString(default__.G__LOW)
        elif (op) == (8):
            return Int.default__.NatToString(default__.G__MID)
        elif (op) == (9):
            return Int.default__.NatToString(default__.G__MID)
        elif (op) == (10):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (11):
            return Int.default__.NatToString(default__.G__LOW)
        elif (op) == (16):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (17):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (18):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (19):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (20):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (21):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (22):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (23):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (24):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (25):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (26):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (27):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (28):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (29):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (32):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (48):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (50):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (51):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (52):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (53):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (54):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (55):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (56):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (57):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (58):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (59):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (60):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (61):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (62):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (63):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (64):
            return Int.default__.NatToString(default__.G__BLOCKHASH)
        elif (op) == (65):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (66):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (67):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (68):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (69):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (70):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (71):
            return Int.default__.NatToString(default__.G__LOW)
        elif (op) == (72):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (80):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (81):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (82):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (83):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (84):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (85):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (86):
            return Int.default__.NatToString(default__.G__MID)
        elif (op) == (87):
            return Int.default__.NatToString(default__.G__HIGH)
        elif (op) == (88):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (89):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (90):
            return Int.default__.NatToString(default__.G__BASE)
        elif (op) == (91):
            return Int.default__.NatToString(default__.G__JUMPDEST)
        elif (op) == (95):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (96):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (97):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (98):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (99):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (100):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (101):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (102):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (103):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (104):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (105):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (106):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (107):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (108):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (109):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (110):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (111):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (112):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (113):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (114):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (115):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (116):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (117):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (118):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (119):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (120):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (121):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (122):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (123):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (124):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (125):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (126):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (127):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (128):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (129):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (130):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (131):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (132):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (133):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (134):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (135):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (136):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (137):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (138):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (139):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (140):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (141):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (142):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (143):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (144):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (145):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (146):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (147):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (148):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (149):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (150):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (151):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (152):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (153):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (154):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (155):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (156):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (157):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (158):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (159):
            return Int.default__.NatToString(default__.G__VERYLOW)
        elif (op) == (160):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (161):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (162):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (163):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (164):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (240):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (241):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (242):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (243):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (244):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (245):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (250):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (253):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif (op) == (255):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Depends on memory expansion"))
        elif True:
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
