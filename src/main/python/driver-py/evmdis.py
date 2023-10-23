#
# Copyright 2023 Franck Cassez
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software dis-
# tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.
#

# Dafny program driver modified to read input from file instead of string.
# Dafny program Driver.dfy compiled into Python
# This file is copied into the output of the Dafny python generator
# If you want to run into another directory, you may have to add the 
# build directory to the os.path before inclding the module, _dafny, and Driver 
import sys
import argparse
import os.path

from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny  

import Driver
try:
    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--file", help="Input filename")
    parser.add_argument("-s", "--string", help="Input string")

    args = parser.parse_args()
    # if arg is a filename, read file in a string
    if args.file:
        print(args.file)
        # check if file exists
        if os.path.isfile(args.file) and os.access(args.file, os.R_OK):
            print("File exists and is readable")
            text_file = open("file.txt", "r")
            # read whole file to a string
            data = text_file.read().strip('\n')
            # close file
            text_file.close()
        else:
            print("Either the file is missing or not readable")
            print("file does not exists or is not readable")
            sys.exit(1)
    # If arg is a string, use the raw string as input
    if args.string:
        data = args.string 

    dafnyArgs = [_dafny.Seq(a) for a in sys.argv]
    # send file as a string or raw string to Dafny input arg number 1
    dafnyArgs[1] = data
    Driver.default__.Main(dafnyArgs)
except _dafny.HaltException as e:
    _dafny.print("[Program halted] " + e.message + "\n")
    sys.exit(1)
