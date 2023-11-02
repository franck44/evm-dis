import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import subprocess
import MiscTypes

# Module: Expect

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def foo(x):
        result = subprocess.run(
        ['dafny','verify', '--stdin'], 
        stdout=subprocess.PIPE,
        # input= ("run --no-verify /Users/franck/development/evm-dis/src/dafny/Driver.dfy --proof " + data).encode('utf-8') 
        input='function f(): nat { 2} ;'.encode('utf-8')
        )
        print(result)
        res = result.stdout.decode('utf-8').split()
        print(res)
        if result.returncode == 0: 
            print(result.stdout.decode('utf-8').split()[4:])
            print("Verified:", res[5])
            print("Errors:", res[7])
        else:
            print("Error!:", result.returncode)
        return result.returncode == 0
    
    @staticmethod
    def foo2(x):
        result = subprocess.run(
        ['dafny','verify', '--stdin'], 
        stdout=subprocess.PIPE,
        # input= ("run --no-verify /Users/franck/development/evm-dis/src/dafny/Driver.dfy --proof " + data).encode('utf-8') 
        input='function f(): nat { 2} ;'.encode('utf-8')
        )
        print(result)
        res = result.stdout.decode('utf-8').split()
        print(res)
        if result.returncode == 0: 
            return MiscTypes.Try_Success(result.returncode)
        else:
             return MiscTypes.Try_Failure(_dafny.Seq("error", True))

    
    

