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

include "../../../src/dafny/utils/StackElement.dfy"
include "../../../src/dafny/utils/State.dfy"
include "../../../src/dafny/utils/LinSegments.dfy"
include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/Hex.dfy"
include "../../../src/dafny/prettyprinters/Pretty.dfy"
  /**
    * Test correct computation of next State.
    * 
    */
module BuilCFGraph {

  import opened OpcodeDecoder
  import opened EVMConstants
  import opened MiscTypes
  import Int
  import Hex
  import opened LinSegments
  import opened State
  import opened StackElement
  import opened BinaryDecoder
  import opened Splitter
  import opened PrettyPrinters

  /**
    *   1. First add path to state 
    *   2. if similar state already encountered check 
    *       whether it covers the new one. Use the most ancient
    *       one.
    *   3. add tests for all states that are similar not only most
    *       ancient one.
    */
  function BuildCFGV3(xs: seq<ValidLinSeg>, maxDepth: nat, numSeg: nat := 0, s: ValidState := DEFAULT_VALIDSTATE, seen: seq<seq<bool>> := [], path: seq<bool> := []): (seq<(seq<bool>, seq<bool>)>, map<seq<bool>,int>)
    requires numSeg < |xs|
    ensures forall k:: k in BuildCFGV3(xs, maxDepth, numSeg, s, seen, path).0 ==> k.0 in BuildCFGV3(xs, maxDepth, numSeg, s, seen, path).1.Keys
    ensures forall k:: k in BuildCFGV3(xs, maxDepth, numSeg, s, seen, path).0 ==> k.1 in BuildCFGV3(xs, maxDepth, numSeg, s, seen, path).1.Keys
    decreases maxDepth

  {
    // if numSeg in marked || maxDepth == 0 then ([], marked)
    if maxDepth == 0 then
      ([ ], map[path := numSeg])
    else if !xs[numSeg].HasExit(false) && !xs[numSeg].HasExit(true) then
      //  no successors
      ([ ], map[path := numSeg])
    else
      //  DFS false
      var leftBranch :=
        if xs[numSeg].HasExit(false) then
          var leftSucc := xs[numSeg].Run(s, false);
          if leftSucc.EState? then
            var nextSeg := PCToSeg(xs, leftSucc.PC());
            if nextSeg.Some? then
              var l := BuildCFGV3(xs, maxDepth - 1, nextSeg.v, leftSucc, seen, path + [false]);
              ([(path, path + [false])] + l.0, l.1)
            else  //  Next segment could not be found
              ([ (path, path + [false]) ], map[path + [false] := -1])
          else // left successor of segment resulted in Error state
            ([ (path, path + [false]) ], map[path + [false] := -1])
        else // no false exit branch expected for this segment
          ([ ], map[]) ;

      assert forall k: (seq<bool>, seq<bool>) :: k in leftBranch.0 ==> k.1 in leftBranch.1.Keys;
      //  DFS true
      var rightBranch :=
        if xs[numSeg].HasExit(true) then
          var rightSucc := xs[numSeg].Run(s, true);
          if rightSucc.EState?  then
            var nextSeg := PCToSeg(xs, rightSucc.PC());
            if nextSeg.Some? then
              var l := BuildCFGV3(xs, maxDepth - 1, nextSeg.v, rightSucc, seen, path + [true]);
              ([(path, path + [true])]  + l.0, l.1)
            else // Next segment could not be found
              ([ (path, path + [true]) ], map[path + [true] := -1])
          else // right successor of segment resulted in Error state
            ([ (path, path + [true]) ], map[path + [true] := -1])
        else //
          ([ ], map[]) ;

      var m : map<seq<bool>, int> := (leftBranch.1 + rightBranch.1)[path := numSeg];
      (leftBranch.0 + rightBranch.0, m)

  }

  function BuildCFGV2(xs: seq<ValidLinSeg>, maxDepth: nat, numSeg: nat := 0, s: ValidState := DEFAULT_VALIDSTATE, marked: set<nat> := {}): (seq<(nat, bool, int)>, set<nat>)
    requires numSeg < |xs|
    decreases maxDepth
  {
    //  
    if numSeg in marked || maxDepth == 0 then ([], marked)
    else
      //  DFS false
      var leftBranch :=
        if xs[numSeg].HasExit(false) then
          var leftSucc := xs[numSeg].Run(s, false);
          if leftSucc.EState? then
            var nextSeg := PCToSeg(xs, leftSucc.PC());
            if nextSeg.Some? then
              var l := BuildCFGV2(xs, maxDepth - 1, nextSeg.v, leftSucc, marked + {numSeg});
              ([(numSeg, false, nextSeg.v)] + l.0, marked + l.1)
            else  //  Next segment could not be found
              ([(numSeg, false, -1)], marked + {numSeg})
          else // left successor of segment resulted in Error state
            ([(numSeg, false, -2)], marked + {numSeg})
        else // no false exit branch expected for this segment
          ([], marked + {numSeg});

      //  DFS true
      var rightBranch :=
        if xs[numSeg].HasExit(true) then
          var rightSucc := xs[numSeg].Run(s, true);
          if rightSucc.EState?  then
            var nextSeg := PCToSeg(xs, rightSucc.PC());
            if nextSeg.Some? then
              var l := BuildCFGV2(xs, maxDepth - 1, nextSeg.v, rightSucc, marked + leftBranch.1 + {numSeg});
              ([(numSeg, true, nextSeg.v)] + l.0, marked + l.1)
            else // Next segment could not be found
              ([(numSeg, true, -1)], marked)
          else // right successor of segment resulted in Error state
            ([(numSeg, true, -2)], marked)
        else //
          ([], marked);
      (leftBranch.0 + rightBranch.0, rightBranch.1)

  }


  function BuildCFG(xs: seq<ValidLinSeg>, maxDepth: nat, numSeg: nat := 0, s: ValidState := DEFAULT_VALIDSTATE, seen: set<nat> := {}): seq<(nat, bool, int)>
    requires numSeg < |xs|
    decreases maxDepth
  {
    //  
    if numSeg in seen || maxDepth == 0 then []
    else
      //  DFS false
      var leftBranch :=
        if xs[numSeg].HasExit(false) then
          var leftSucc := xs[numSeg].Run(s, false);
          if leftSucc.EState? then
            var nextSeg := PCToSeg(xs, leftSucc.PC());
            if nextSeg.Some? then
              var l := BuildCFG(xs, maxDepth - 1, nextSeg.v, leftSucc, seen + {numSeg});
              [(numSeg, false, nextSeg.v)] + l
            else  //  Next segment could not be found
              [(numSeg, false, -1)]
          else // left successor of segment resulted in Error state
            [(numSeg, false, -2)]
        else // no false exit branch expected for this segment
          [];

      //  DFS true
      var rightBranch :=
        if xs[numSeg].HasExit(true) then
          var rightSucc := xs[numSeg].Run(s, true);
          if rightSucc.EState?  then
            var nextSeg := PCToSeg(xs, rightSucc.PC());
            if nextSeg.Some? then
              var l := BuildCFG(xs, maxDepth - 1, nextSeg.v, rightSucc, seen + {numSeg});
              [(numSeg, true, nextSeg.v)] + l
            else // Next segment could not be found
              [(numSeg, true, -1)]
          else // right successor of segment resulted in Error state
            [(numSeg, true, -2)]
        else //
          [];
      leftBranch + rightBranch

  }


  //   predicate HasExit(s: ValidLinSeg, b: bool)
  //   {
  //     match s
  //     case JUMPSeg(_, _, _) => b
  //     case JUMPISeg(_, _, _) => true
  //     case CONTSeg(_, _, _)  => !b
  //     case _ => false
  //   }

  function PCToSeg(xs: seq<ValidLinSeg>, pc: nat, rank: nat := 0): (r: Option<nat>)
    requires rank <= |xs|
    ensures r.Some? ==> r.v < |xs|
    decreases |xs| - rank
  {
    if rank == |xs| then None
    else if xs[rank].StartAddress() == pc then Some(rank)
    else PCToSeg(xs, pc, rank + 1)
  }

  function GetSuccSeg(l: ValidLinSeg, s: ValidState, exit: bool): Option<AState>
  {
    match l
    case JUMPSeg(_, _, _) => if exit then Some(l.Run(s, exit)) else None
    case JUMPISeg(_, _, _) => Some(l.Run(s, exit))
    case _  => if !exit then Some(l.Run(s, exit)) else None
  }

  method PrintEdges(xe: seq<(nat, bool, int)>) {
    if |xe| > 0 {
      if xe[0].2 >= 0 {
        print "s", xe[0].0, " -> s", xe[0].2, " [label=", xe[0].1, "]\n";
      } else {
        print "s", xe[0].0, " -> END/ERROR", " [label=", xe[0].1, "]\n";
      }
      PrintEdges(xe[1..]);
    }
  }

  function foo(x: seq<bool>): string
  {
    if |x| == 0 then "E"
    else
      [if x[0] then '1' else '0'] + foo(x[1..])
  }

  function foo101(x: seq<bool>): string
    requires |x| > 0
  {
    if x[|x| - 1] then "true" else "false"
  }

  method PrintEdgesV3(xe: seq<(seq<bool>, seq<bool>)>, m: map<seq<bool>, int>)
    requires forall k:: k in xe ==> k.0 in m.Keys
    requires forall k:: k in xe ==> k.1 in m.Keys
  {
    if |xe| > 0 {
      if |xe[0].1| > 0 {
        print "s", foo(xe[0].0), " -> s", foo(xe[0].1), " [label=", foo101(xe[0].1), "]\n";
      } else {
        //  Error/End state
        print "s", foo(xe[0].0), " -> ENDERROR", " [label=", "end", "]\n";
      }
      //   PrintPaths(xe[0]);
      assert forall k:: k in xe[1..] ==> k in xe;
      PrintEdgesV3(xe[1..], m);
    }
  }

  //   function CollectSeq(s: seq<seq<bool>>, n: nat := 0, collected: seq<seq<bool>>): (r: seq<seq<bool>>)
  //     requires n <= |s|
  //     requires forall k:: k in s[..n] ==> k in collected
  //     decreases |s| - n
  //   {
  //     if |s| == 0 || n == |s| then collected
  //     else if s[0] in collected then
  //       CollectSeq(s, n + 1)
  //     else
  //       CollectSeq(s + [s[0]] , n + 1)
  //   }

  //   function CollectNodes(xe: seq<(seq<bool>, seq<bool>)>, collected: seq<seq<bool>> := []): (r: seq<seq<bool>>)
  //     ensures forall k:: k in xe ==> k.0 in r
  //   {
  //     if |xe| == 0 then collected
  //     else
  //       var e := if xe[0].0 !in collected then collected + [xe[0].0] else collected;
  //       var e' := if xe[0].1 !in e then e + [xe[0].1] else e;
  //       assert xe[0].1 in e';
  //       e' + CollectNodes(xe[1..], e')
  //   }

  function CollectNodes<T(==)>(xe: seq<T>, collected: seq<T> := []): (r: seq<T>)
    ensures forall k:: k in xe ==> k in r
  {
    // xe
    if |xe| == 0 then collected
    else
      var e := if xe[0] !in collected then collected + [xe[0]] else collected;
      e + CollectNodes(xe[1..], e)
  }

  function CollectNodes2<T(!new)(==)>(xe: seq<(T, T)>, collected: seq<T> := [], n: nat := 0): (r: seq<T>)
    requires n <= |xe|
    requires forall k:: k in xe[..n] ==> k.0 in collected && k.1 in collected
    // requires forall k:: k in collected ==> (exists l:: l in xe[..n] && (k == l.0 || k == l.1))
    requires forall k, k'::0 <= k < k' < |collected| ==> collected[k] != collected[k']
    ensures forall k:: k in xe ==> k.0 in r && k.1 in r
    decreases |xe| - n
  {
    if |xe| == n then collected
    else
      var e := if xe[n].0 !in collected then collected + [xe[n].0] else collected;
      var e' := if xe[n].1 !in e then e + [xe[n].1] else e;
      //   assert
      CollectNodes2(xe, e', n + 1)
  }

  method PrintPaths(xs: seq<bool>, num: nat := 0)
    requires num <= |xs|
  {
    if |xs| - num > 1 {
      print "s", foo(xs[..num]), " -> s", foo(xs[..num + 1]), " [label=", xs[num + 1], "]\n";
    }
  }

  method PrintToDot(xs: seq<ValidLinSeg>, xe: seq<(nat, bool, int)>) {
    print "digraph CFG", "\n";
    print "{", "\n";
    print "node [shape=box]\n";
    //  Print nodes content
    PrintNodes(xs);
    PrintEdges(xe);
    print "}", "\n";

  }

  method PrintToDotV3(xs: seq<ValidLinSeg>, xe: seq<(seq<bool>, seq<bool>)>, m: map<seq<bool>, int>)
    requires forall k:: k in xe ==> k.0 in m.Keys
    requires forall k:: k in xe ==> k.1 in m.Keys
  {
    print "digraph CFG", "\n";
    print "{", "\n";
    print "node [shape=box]\n";
    //  Print nodes content
    var n := CollectNodes2(xe);

    PrintNodesV3(xs, xe, m); 
    PrintEdgesV3(xe, m);
    print "}", "\n";
  }

  method PrintNodesV3(xs: seq<ValidLinSeg>, xe: seq<(seq<bool>, seq<bool>)>, m: map<seq<bool>, int>, printed: set<seq<bool>> := {})
    requires forall k:: k in xe ==> k.0 in m.Keys
    requires forall k:: k in xe ==> k.1 in m.Keys
  {
    if |xe| > 0 {
      //  check and print .0 component
      if xe[0].0 !in printed {
        var numSeg := m[xe[0].0];
        if 0 <= numSeg < |xs| {
          var seg := xs[numSeg];
          print "s", foo(xe[0].0), "[label=<", "Segment ", numSeg, " 0x", Hex.NatToHex(seg.StartAddress()), "<BR ALIGN=\"CENTER\"/>\n";
          for k := 0 to |seg.ins| {
            print seg.ins[k].ToString(), "<BR ALIGN=\"LEFT\"/>\n";
          }
          print seg.lastIns.ToString(), "<BR ALIGN=\"LEFT\"/>\n";
          print ">]\n";
        } else {
          print "s", foo(xe[0].1), "[label=<", "ErrorEnd ", "<BR ALIGN=\"CENTER\"/>\n";
        }
      }
      //   var newPrinted := printed + {xe[0].0};
      if xe[0].1 !in printed && xe[0].1 != xe[0].0 {
        var numSeg: int := m[xe[0].1];
        if 0 <= numSeg < |xs| {
          var seg := xs[numSeg];
          print "s", foo(xe[0].1), "[label=<", "Segment ", numSeg, " 0x", Hex.NatToHex(seg.StartAddress()), "<BR ALIGN=\"CENTER\"/>\n";
          for k := 0 to |seg.ins| {
            print seg.ins[k].ToString(), "<BR ALIGN=\"LEFT\"/>\n";
          }
          print seg.lastIns.ToString(), "<BR ALIGN=\"LEFT\"/>\n";
          print ">]\n";
        } else {
          //  -1 Error or end node
          print "s", foo(xe[0].1), "[label=<", "ErrorEnd ", "<BR ALIGN=\"CENTER\"/>\n";
        }
      }

      assert forall k:: k in xe[1..] ==> k in xe;
      PrintNodesV3(xs, xe[1..], m, printed + {xe[0].0, xe[0].1});
    }
  }

  method PrintNodes(xs: seq<ValidLinSeg>, n: nat := 0)
    requires n <= |xs|
    decreases |xs| - n
  {
    if n < |xs| {
      // Hex.NatToHex(xs[0].StartAddress())

      print "s", n, "[label=<", "Segment ", n, " 0x", Hex.NatToHex(xs[n].StartAddress()), "<BR ALIGN=\"CENTER\"/>\n";
      for k := 0 to |xs[n].ins| {
        print xs[n].ins[k].ToString(), "<BR ALIGN=\"LEFT\"/>\n";
      }
      print xs[n].lastIns.ToString(), "<BR ALIGN=\"LEFT\"/>\n";
      print ">]\n";
      //   PrintSegments([xs[0]]);
      PrintNodes(xs, n + 1);
    }
  }



}

