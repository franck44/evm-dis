import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: MiscTypes

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Foobar(f):
        return True

    @staticmethod
    def Last(x):
        return (x)[(len(x)) - (1)]

    @staticmethod
    def Drop(x, n):
        return _dafny.SeqWithoutIsStrInference((x)[n::])

    @staticmethod
    def Init(x):
        return _dafny.SeqWithoutIsStrInference((x)[:(len(x)) - (1):])

    @staticmethod
    def Zip(u, v):
        return _dafny.SeqWithoutIsStrInference([((u)[d_0_i_], (v)[d_0_i_]) for d_0_i_ in range(len(u))])

    @staticmethod
    def UnZip(x):
        d_0_x0_ = _dafny.SeqWithoutIsStrInference([((x)[d_1_i_])[0] for d_1_i_ in range(len(x))])
        d_2_x1_ = _dafny.SeqWithoutIsStrInference([((x)[d_3_i_])[1] for d_3_i_ in range(len(x))])
        return (d_0_x0_, d_2_x1_)

    @staticmethod
    def Filter(u, f):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(u)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif f((u)[0]):
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([(u)[0]]))
                    in0_ = _dafny.SeqWithoutIsStrInference((u)[1::])
                    in1_ = f
                    u = in0_
                    f = in1_
                    raise _dafny.TailCall()
                elif True:
                    in2_ = _dafny.SeqWithoutIsStrInference((u)[1::])
                    in3_ = f
                    u = in2_
                    f = in3_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Exists(xs, f):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return False
                elif f((xs)[0]):
                    return True
                elif True:
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in1_ = f
                    xs = in0_
                    f = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Flatten(x):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + ((x)[0])
                    in0_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    x = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Map(t, f):
        return _dafny.SeqWithoutIsStrInference([f((t)[d_0_i_]) for d_0_i_ in range(len(t))])

    @staticmethod
    def MapP(t, f):
        return _dafny.SeqWithoutIsStrInference([f((t)[d_0_i_]) for d_0_i_ in range(len(t))])

    @staticmethod
    def FoldLeft(t, u0, f):
        while True:
            with _dafny.label():
                if (len(t)) == (0):
                    return u0
                elif True:
                    in0_ = _dafny.SeqWithoutIsStrInference((t)[1::])
                    in1_ = f(u0, (t)[0])
                    in2_ = f
                    t = in0_
                    u0 = in1_
                    f = in2_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SeqToSet(t):
        d_0___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (len(t)) == (0):
                    return (_dafny.Set({})) | (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) | (_dafny.Set({(t)[0]}))
                    in0_ = _dafny.SeqWithoutIsStrInference((t)[1::])
                    t = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Find(x, t):
        return default__.FindRec(x, t, 0)

    @staticmethod
    def FindRec(x, t, i):
        while True:
            with _dafny.label():
                if (len(x)) == (0):
                    return Option_None()
                elif ((x)[0]) == (t):
                    return Option_Some(i)
                elif True:
                    in0_ = _dafny.SeqWithoutIsStrInference((x)[1::])
                    in1_ = t
                    in2_ = (i) + (1)
                    x = in0_
                    t = in1_
                    i = in2_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def AddKeyVal(m, key, val):
        return (m).set(key, ((m)[key]) + (_dafny.SeqWithoutIsStrInference([val])))


class Try:
    @classmethod
    def default(cls, ):
        return lambda: Try_Failure(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Success(self) -> bool:
        return isinstance(self, Try_Success)
    @property
    def is_Failure(self) -> bool:
        return isinstance(self, Try_Failure)

class Try_Success(Try, NamedTuple('Success', [('v', Any)])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Try.Success({_dafny.string_of(self.v)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Try_Success) and self.v == __o.v
    def __hash__(self) -> int:
        return super().__hash__()

class Try_Failure(Try, NamedTuple('Failure', [('msg', Any)])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Try.Failure({self.msg.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Try_Failure) and self.msg == __o.msg
    def __hash__(self) -> int:
        return super().__hash__()


class Option:
    @classmethod
    def default(cls, ):
        return lambda: Option_None()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_None(self) -> bool:
        return isinstance(self, Option_None)
    @property
    def is_Some(self) -> bool:
        return isinstance(self, Option_Some)
    def Extract(self):
        return (self).v


class Option_None(Option, NamedTuple('None_', [])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Option.None'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_None)
    def __hash__(self) -> int:
        return super().__hash__()

class Option_Some(Option, NamedTuple('Some', [('v', Any)])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Option.Some({_dafny.string_of(self.v)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_Some) and self.v == __o.v
    def __hash__(self) -> int:
        return super().__hash__()


class Either:
    @classmethod
    def default(cls, default_T):
        return lambda: Either_Left(default_T())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Left(self) -> bool:
        return isinstance(self, Either_Left)
    @property
    def is_Right(self) -> bool:
        return isinstance(self, Either_Right)
    def Left(self):
        return (self).l

    def Right(self):
        return (self).r


class Either_Left(Either, NamedTuple('Left', [('l', Any)])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Either.Left({_dafny.string_of(self.l)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Either_Left) and self.l == __o.l
    def __hash__(self) -> int:
        return super().__hash__()

class Either_Right(Either, NamedTuple('Right', [('r', Any)])):
    def __dafnystr__(self) -> str:
        return f'MiscTypes.Either.Right({_dafny.string_of(self.r)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Either_Right) and self.r == __o.r
    def __hash__(self) -> int:
        return super().__hash__()


class WellDefined:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        def lambda0_(d_0_x_, d_1_xs_):
            return Option_None()

        return lambda0_

class WellDefined2:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        def lambda1_(d_2_x_, d_3_xs_):
            return Option_None()

        return lambda1_

class Foo:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        def lambda2_(d_4_x_):
            return 0

        return lambda2_
