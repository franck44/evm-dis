/*
 * Copyright 2023 Franck Cassez
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

/**
  * Provides Option type.
  */
module MiscTypes {

  datatype Try<T> = Success(v: T) | Failure(msg: string)

  datatype Option<T> = None | Some(v: T)
  {
    function Extract(): T
      requires this.Some?
    {
      this.v
    }
  }

  datatype Either<T, U> = Left(l: T) | Right(r: U)
  {
    function Left(): T
      requires this.Left?
    {
      this.l
    }

    function Right(): U
      requires this.Right?
    {
      this.r
    }
  }

  function Zip<U, V>(u: seq<U>, v: seq<V>): seq<(U, V)>
    requires |u| == |v|
  {
    seq(|u|, i requires 0 <= i < |u| => (u[i], v[i]))
  }

  function UnZip<U, V>(x: seq<(U, V)>): (seq<U>, seq<V>)
    ensures |UnZip(x).0| == |UnZip(x).1| == |x|
    ensures forall k:: 0 <= k < |x| ==> (UnZip(x).0[k] == x[k].0 && UnZip(x).1[k] == x[k].1)
  {
    var x0 := seq(|x|, i requires 0 <= i < |x| => x[i].0);
    var x1 := seq(|x|, i requires 0 <= i < |x| => x[i].1);
    (x0 ,x1)
  }

  function Filter<U>(u: seq<U>, f: U -> bool): (r: seq<U>)
    ensures |r| <= |u|
    ensures forall x:: x in r ==> x in u
    ensures forall k:: 0 <= k < |r| ==> f(r[k]) 
    ensures forall x:: x in r ==> f(x)
  {
    if |u| == 0 then [] 
    else if f(u[0]) then [u[0]] + Filter(u[1..], f)
    else Filter(u[1..], f)
  }

}