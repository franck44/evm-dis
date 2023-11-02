import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import MiscTypes
import subprocess
import os

# Module: Expect
class default__:
    def  __init__(self):
        pass

    @staticmethod
    def verifyProg(x):
        # _dafny.print("Hello" + x)
        DAFNY_HOME = USER = os.getenv('DAFNY_HOME')
        print(DAFNY_HOME)
        # print("Hello " + _dafny.string_of(x))
        # print(_dafny.string_of(x))
        # z = _dafny.string_of(x)
        # print(z)
        y = "".join([str(i) for i in x])

        # x="".join([str(i) for i in s])

        # print(y)
        # return False
        result = subprocess.run(
            # ['pwd'],
        [DAFNY_HOME + 'dafny','verify', '--stdin'], 
        stdout=subprocess.PIPE,
        # input= ("run --no-verify /Users/franck/development/evm-dis/src/dafny/Driver.dfy --proof " + data).encode('utf-8') 
        input=y.encode('utf-8')
        )
        print(result)
        res = result.stdout.decode('utf-8').split()
        # return False
        print(res)
        if result.returncode == 0: 
            print(result.stdout.decode('utf-8').split()[4:])
            print("Verified:", res[5])
            print("Errors:", res[7])
        else:
            print("Error!:", result.returncode)
        return result.returncode == 0

