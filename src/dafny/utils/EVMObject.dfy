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

include "../utils/LinSegments.dfy"
include "../utils/CFGState.dfy"
include "../utils/State.dfy"
include "../utils/MiscTypes.dfy"
include "../utils/Instructions.dfy"
include "../utils/int.dfy"
include "../proofobjectbuilder/SegmentBuilder.dfy"
include "../utils/Hex.dfy"
include "../utils/Automata.dfy"
include "../utils/Partition.dfy"
include "../utils/Statistics.dfy"
include "../utils/MinimiserGState.dfy"
include "../utils/HTML.dfy"

/**
  *  Provides EVM Object.
  *  An EVM object is a list of segments together with some 
  *  additional information e.g. the jumpDests in the segments.
  */
module EVMObject {

  import opened LinSegments
  import opened CFGState
  import opened State
  import opened MiscTypes
  import Instructions
  import Int
  import SegBuilder
  import Hex
  import opened Automata
  import opened PartitionMod
  import opened GStateMinimiser
  import opened WeakPre
  import opened StackElement
  import opened Statistics
  import opened HTML

  /**
    * A path is a sequence of states and a sequence of exits.
    */
  datatype Path<T(!new)> = Path(states: seq<T>, exits: seq<nat>)

  /**
    *    A valid sequence of valid linear segments. To be valid the sequence 
    *    must be ordered by start addresses.
    */
  type ValidSeqValidLinSeg = xs: seq<ValidLinSeg> |
      forall i, i':: 0 <= i < i' < |xs| ==> xs[i].StartAddress() < xs[i'].StartAddress()

  /**   A valid EVMObj should have a PCToSegMap that is the reverse of xs -> startAddress() . */
  type ValidEVMObj = e: EVMObj | e.IsValid() witness EVMObj([], [])

  /**   An EVMObj has segments and jumpDests. */
  datatype EVMObj = EVMObj(
    xs: ValidSeqValidLinSeg,
    jumpDests: seq<nat> := CollectJumpDests(xs),
    PCToSegMap: map<nat, nat> := CollectThem(xs)
    // PCToSegMap: map<nat, nat> := CollectPCToSeg(xs) . does not work with VsCode plugin ...hangs up
  ) {

    /** A valid EVMObj has jumpDests consistent with xs. */
    ghost predicate IsValid() {
      && (forall i, i':: 0 <= i < i' < |xs| ==> xs[i].StartAddress() < xs[i'].StartAddress())
      && (forall k:: k in PCToSegMap ==> PCToSegMap[k] < |xs| && xs[PCToSegMap[k]].StartAddress() == k)
    }

    /**
      *  Helper to provide the start address of a segment,
      */
    function StartAddress(i: nat): nat
      requires i < |xs|
    {
      xs[i].StartAddress()
    }

    /** The size of the program in bytes. */
    function Size(ls: seq<ValidLinSeg> := xs): nat {
      if |ls| == 0 then 0
      else ls[0].Size() + Size(ls[1..])
    }

    /**
      * Compute the next abstract states from a given abstract state.
      * @param s The abstract state.
      * @returns The next abstract states.
      *
      * @note   This function is _inductive_ in the sense of the Inductive predicate (see BuildCFG).
      */
    function {:opaque} NextG(s: GState): (r: seq<GState>)
      requires this.IsValid()
      requires s.IsBounded(|xs|)
      ensures forall k:: 0 <= k < |r| ==> r[k].IsBounded(|xs|)
      ensures |r| > 0 ==> s.EGState?
      ensures  s.EGState?  ==> |r| == xs[s.segNum].NumberOfExits()
      ensures s.ErrorGState? ==> |r| == 0
    {
      match s
      case ErrorGState(_) => []
      case EGState(segNum, st) =>
        // compute next state
        var srcSeg := xs[segNum];
        var src: AState := EState(srcSeg.StartAddress(), st);
        var successors := seq(srcSeg.NumberOfExits(), (i: nat) requires srcSeg.IsValidExit(i) => srcSeg.Run(src, i, jumpDests));
        //  map to GState when PCToSegMap is defined
        var succGStates :=
          Map(
            successors,
            (s': AState) =>
              match s'
              case Error(msg) => ErrorGState(msg)
              case EState(pc, st) =>
                if pc in PCToSegMap then
                  EGState(PCToSegMap[pc], s'.stack)
                else
                  ErrorGState("NextG:  " + Int.NatToString(pc) + " not defined")
          );
        succGStates
    }

    /**   Execute a sequence of segments.
      *
      *   @param  exist       Exists after each segment.
      *   @param  s           A state.
      *
      */
    function {:opaque} RunAll(exits: seq<nat>, s: AState): AState
      requires this.IsValid()
      requires s.EState?
    {
      if |exits| == 0 then s
      else if s.pc in PCToSegMap then
        var seg := PCToSegMap[s.pc];
        if xs[seg].NumberOfExits() > exits[0] then
          ValidExitLemma(xs[seg], exits[0]);
          var s' := xs[seg].Run(s, exits[0], jumpDests);
          if s'.EState? then
            // Run the rest of the path
            RunAll(exits[1..], s')
          else
            //  exit does not exist, return the error state.
            Error("Successor state of " + s.ToString() + " is not an EState")
        else
          //  exit does not exist
          Error("Exit does not exist")
      else
        Error("No segment found for state " + s.ToString())
    }

    /**
      *   Whether a condition is invariant under a given path.
      *   @param  c           A condition.
      *   @param  exits       The exit after each segment.
      */
    predicate {:opaque} PreservesCond(c: ValidCond, exits: seq<nat>, initpc: nat)
      requires this.IsValid()
      requires c.StCond?
    {
      var initState := BuildInitState(c).(pc := initpc);
      var endState := RunAll(exits, initState);
      if endState.EState? then
        endState.Sat(c)
      else false
    }

    /**
      *   Check if a segment has been found on a path, If it has been found,
      *   check if the path is inductive, i.e. if the weakest precondition is invariant 
      *   on the path from the state occurrenc to the end of the path.
      *   @param  i           The segment number to find.
      *   @param p            The path to check. The path should be such that 
      *                       the last state is an EGState and the segment number is i.
      *   @returns            The state that covers the last one, or None if no covering. 
      *
      *   @note   The seenOnPath has all the nodes seen before the current one.
      *           The current one has startAddress == pc.
      */
    function SafeLoopFound(i: nat, pStates: seq<GState>, pExits: seq<nat>): (r: (Option<nat>))
      requires this.IsValid()
      requires i < |xs|
      requires  |pStates| == |pExits|
      requires forall s:: s in pStates ==> s.EGState? && s.IsBounded(|xs|)
      requires forall k:: 0 <= k < |pExits| ==> pExits[k] < |NextG(pStates[k])|

      ensures r.Some? ==> r.v < |pStates|
      decreases |pStates|
    {
      match FindFirstNodeWithSegIndex(i, pStates)
      case Some(index) =>
        //  The segment of pStates[index]
        assert index < |pStates|;
        assert pStates[index].segNum == i;
        //  Get the states/exits on the path from index to end
        var pathFromIndex := pStates[index..];
        assert pathFromIndex[0].segNum == i;
        var exitsFromIndex := pExits[index..];
        //  Map to the segment numbers
        var segmentsOnPathFromIndex := seq(|pathFromIndex|, i requires 0 <= i < |pathFromIndex| => pathFromIndex[i].segNum);
        //  Tgt pos condition is that the last node leads to the startAddress of segment i
        var tgtCond := xs[Last(pStates).segNum].LeadsTo(xs[i].StartAddress(), Last(pExits));
        //  compute the Wpre of the tgtCond for the path from index to end
        var w1 := WPreSeqSegs(segmentsOnPathFromIndex, exitsFromIndex, tgtCond, xs, xs[i].StartAddress());
        if w1.StTrue? then
          Some(index)
        else if w1.StFalse? then
          None
        else if PreservesCond(w1, exitsFromIndex, xs[i].StartAddress()) then
          Some(index)
        //  Try a potential second occurrence of segment i on the path
        else if 0 < |pathFromIndex| then // < |pStates| then
          assert forall i:: 0 <= i < |exitsFromIndex| ==> exitsFromIndex[i] < |NextG(pathFromIndex[i])|;
          SafeLoopFound(i, pathFromIndex[1..], exitsFromIndex[1..])
        else None

      // no occurrence of segment i on this path
      case None => None
    }

    /**
      *   Find the first node in a sequence with a givem value for pc.
      *   @param  i       The segment number to find
      *   @param  gs      A sequence of states.
      *   @param  index   The current index in the search.
      *   @returns        The index of the first state in xs with a segment 
      *                   number equal to i if any and None otherwise.
      */
    function FindFirstNodeWithSegIndex(i: nat, gs: seq<GState>, index: nat := 0): (r: Option<nat>)
      requires index <= |gs|
      requires forall s:: s in gs ==> s.EGState?
      ensures r.Some? ==> r.v < |gs| && gs[r.v].segNum == i
      decreases |gs| - index
    {
      if |gs| == index then None
      else
        match gs[index]
        case EGState(i', st) =>
          if i' == i then Some(index)
          else FindFirstNodeWithSegIndex(i, gs, index + 1)
        case ErrorGState(m) => None
    }

    /** 
      * Build the CFG of the EVMObj.
      * The CFG is built by running a DFS from the initial state.
      * @param maxDepth The maximum depth of the DFS.
      * @param minimise If true, the CFG is minimised.   
      */
    method {:timeLimitMultiplier 2} DFS(
      p: Path<GState>,
      a: ValidAuto<GState>,
      maxDepth: nat := 0,
      debugInfo: bool := false,
      stats: Stats := Stats()) returns (a': ValidAuto<T>, stats': Stats)

      requires this.IsValid()
      requires  |p.states| == |p.exits| + 1
      requires forall s:: s in p.states ==> s in a.states
      requires forall s:: s in a.states ==> s.IsBounded(|xs|)
      requires forall s:: s in p.states ==> s.EGState?
      requires (forall k:: 0 <= k < |p.exits| ==> p.exits[k] < |NextG(p.states[k])|)
      requires (forall k:: 0 <= k < |p.exits| ==> p.states[k + 1] == NextG(p.states[k])[p.exits[k]])

      ensures forall s:: s in p.states ==> s in a'.states
      ensures forall s:: s in a'.states ==> s.IsBounded(|xs|)

      decreases maxDepth
    {
      var LastOnPath := Last(p.states);
      if maxDepth == 0 || LastOnPath.ErrorGState? {
        //  stop the construction of the automaton.
        var stats' := if maxDepth == 0 then stats.SetMaxDepth() else stats;
        return a, stats';
      }
      else {
        // DFS from last state on the path
        a' := a;
        stats' := stats;
        for i := 0 to |NextG(LastOnPath)|
          invariant a'.IsValid()
          invariant forall s:: s in a'.states ==> NextG.requires(s)
          invariant forall s:: s in p.states ==> s in a'.states
        {
          var i_th_succ := NextG(LastOnPath)[i];
          if i_th_succ.ErrorGState? {
            a', stats' := a'.AddEdge(LastOnPath, i_th_succ), stats'.IncError();
          } else if i_th_succ in a'.indexOf {
            a', stats' := a'.AddEdge(LastOnPath, a'.states[a'.indexOf[i_th_succ]]), stats'.IncVisited();
          } else if !xs[LastOnPath.segNum].IsJump() {
            //  not already seen and not a jump
            assert i_th_succ !in a'.indexOf;
            a', stats' := DFS(
              Path(p.states + [i_th_succ], p.exits + [i]),
              a'.AddEdge(LastOnPath, i_th_succ),
              maxDepth - 1,
              debugInfo,
              stats');
          } else {
            assert i_th_succ.EGState?;
            match SafeLoopFound(i_th_succ.segNum, p.states, p.exits + [i]) {
              case Some(index) =>
                //  s' is the state that covers LastOnPath
                a', stats' := a'.AddEdge(LastOnPath, p.states[index]), stats'.IncWpre();
              case None =>
                //  not already seen and not covered
                a', stats' := DFS(
                  Path(p.states + [i_th_succ], p.exits + [i]),
                  a'.AddEdge(LastOnPath, i_th_succ),
                  maxDepth - 1,
                  debugInfo,
                  stats');
            }
          }
        }
      }
    }

    /** 
      * Build the CFG of the EVMObj.
      * The CFG is built by running a DFS from the initial state.
      * @param maxDepth The maximum depth of the DFS.
      * @param minimise If true, the CFG is minimised.   
      */
    method {:opaque} BuildCFG(maxDepth: nat := 100, minimise: bool := true) returns (a: Automata.ValidAuto<GState>, stats: Stats)
      requires this.IsValid()
      requires |xs| >= 1
      ensures forall s:: s in a.states && s.EGState? ==> s.segNum < |xs|
    {
      //  For now we ignore the history
      var a1, s1 := DFS(
        Path([DEFAULT_GSTATE], []),
        Automata.Auto().AddState(DEFAULT_GSTATE),
        maxDepth,
        true);

      if !minimise || a1.SSize() == 0 {
        return a1, s1;
      } else {
        //  Minimise the automaton
        var p1: ValidPartition := PartitionMod.MakeInit(a1.SSize());
        //  create an equivalence relation on nodes
        var e :=
          (x:nat, y:nat) requires 0 <= x < a1.SSize() && 0 <= y < a1.SSize()
          => if x == y then
              true
            else
              match (a1.states[x], a1.states[y])
              case (EGState(s1,_), EGState(s2, _)) => s1 == s2
              case (_, _) => false
          ;
        assert IsEquivRel(e, a1.SSize());
        var p2 := p1.ComputeFinest(e);

        var vp: GStateMinimiser.Pair := Pair(a1, p2);
        var a2 := vp.Minimise();
        return a2, s1.(nonMinimisedSize := (a1.SSize(), a1.TSize()));
      }
    }

    /**
      * Generate the HTML representation of a given abstract state.
      */
    function {:opaque} ToHTML(a: GState, withTable: bool := false): string
      requires this.IsValid()
      requires a.IsBounded(|xs|) // a.EGState? ==> a.segNum < |xs|
    {
      //  if s.EGState?, because of the pre-condition, we are sure that a has a segNum < |xs|
      //  and we can use xs[a.segNum]
      if a.ErrorGState? then
        "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"
      else if withTable then
        "<" + DOTSegTable(xs[a.segNum], a.segNum) +">"
      else
        "<" + DOTSeg(xs[a.segNum], a.segNum).0 +">"
    }

    /**
      *  Generate a DOT edge's label.
      */
    function DotLabel(s: GState, exit: nat): string
      requires this.IsValid()
      requires s.IsBounded(|xs|)
    {
      var lab := if s.ErrorGState? then
                   "Error"
                 else if s.EGState? && exit < xs[s.segNum].NumberOfExits() then
                   if xs[s.segNum].IsJump() && exit == xs[s.segNum].NumberOfExits() - 1 then
                     "tooltip=\"Jump\",style=dashed"
                   else
                     "tooltip=\"Next\""
                 else
                   "Error Number of exits"
        ;
      " [" + lab + "]"
    }

    /**
     *  Print info for the bytecode.
     */
    method {:print} PrintByteCodeInfo() {
      var listIns: seq<Instructions.ValidInstruction> :=  Flatten(Map(xs, (s: ValidLinSeg) => s.Ins()));
      print "Bytecode Size: ", Size(), " Bytes\n";
      print "Number of instructions: ", |listIns|, "\n";
      print "Arithmetic opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.ArithOp?)|, "\n";
      print "Comparison opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.CompOp?)|, "\n";
      print "Bitwise opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.BitwiseOp?)|, "\n";
      print "Keccak opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.KeccakOp?)|, "\n";
      print "Environmental opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.EnvOp?)|, "\n";
      print "Storage opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.StorageOp?)|, "\n";
      print "Memory opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.MemOp?)|, "\n";
      print "Stack opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.StackOp?)|, "\n";
      print "Jump opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.JumpOp?)|, "\n";
      print "Log opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.LogOp?)|, "\n";
      print "Revert/stop opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.SysOp? && i.op.IsRevertStop())|, "\n";
      print "Return opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.SysOp? && i.op.IsReturn())|, "\n";
      print "Invalid opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.SysOp? && i.op.IsInvalid())|, "\n";
      print "Other Systems opcodes: ", |Filter(listIns, (i: Instructions.ValidInstruction) => i.op.SysOp? && !i.op.IsInvalid() && !i.op.IsRevertStop() && !i.op.IsReturn())|, "\n";
    }

    /**
     *  Print info for the segnments of the bytecode.
     */
    method PrintSegmentInfo() {
        print "Total number of segments: ", |xs|, "\n";
        print "# of JUMP segments: ", |Filter(xs, (s: ValidLinSeg) => s.JUMPSeg?)|, "\n";
        print "# of JUMPI segments: ", |Filter(xs, (s: ValidLinSeg) => s.JUMPISeg?)|, "\n";
        print "# of RETURN segments: ", |Filter(xs, (s: ValidLinSeg) => s.RETURNSeg?)|, "\n";
        print "# of STOP segments: ", |Filter(xs, (s: ValidLinSeg) => s.STOPSeg?)|, "\n";
        print "# of CONT segments: ", |Filter(xs, (s: ValidLinSeg) => s.CONTSeg?)|, "\n";
        print "# of INVALID segments: ", |Filter(xs, (s: ValidLinSeg) => s.INVALIDSeg?)|, "\n";
    }

  }


  /** Collect jumpdests in a list of segments.  */
  function {:opaque} CollectJumpDests(xs: seq<ValidLinSeg>): seq<nat> {
    if |xs| == 0 then []
    else
      xs[0].CollectJumpDest() + CollectJumpDests(xs[1..])
  }

  /**
    *  Collect the mapping from PC to segment number.
    *  @note This is essentially the same as CollectPCToSeg but with less pre-conditions.
    *        This function is called in the constructor of an EVMObj. 
    *        The CollectPCToSeg causes the VsCode Dafny server to hang for ever.
    *        When/if this bug is fixed we can use PCToSegMap in the constructor of EVMObj.
    * @note  The CLI version of Dafny does not hang and verifies the code.
    */
  function {:opaque} CollectThem(xs: seq<ValidLinSeg>): (r: map<nat, nat>)
    requires forall i, i':: 0 <= i < i' < |xs| ==> xs[i].StartAddress() < xs[i'].StartAddress()
    ensures forall k:: 0 <= k < |xs| ==> xs[k].StartAddress() in r && r[xs[k].StartAddress()] == k
    ensures forall k:: k in r ==> r[k] < |xs| && xs[r[k]].StartAddress() == k
  {
    CollectPCToSeg(xs)
  }

  /** 
    *  Collect the mapping from PC to segment number.
    *  @param  xs      A list of segments.
    *  @param  m       The part of the map that has been built so far. 
    *  @param  index   The current index in the list of segments.
    *  @returns        The map from PC to segment number.
    *  @note           The resulkt satisfies some properties given by the ensures clauses.
    */
  function {:opaque} CollectPCToSeg(xs: seq<ValidLinSeg>, m: map<nat, nat> := map[], index: nat := 0): (r: map<nat, nat>)
    requires index <= |xs|
    requires forall i, i':: 0 <= i < i' < |xs| ==> xs[i].StartAddress() < xs[i'].StartAddress()
    requires forall k:: 0 <= k < index ==> xs[k].StartAddress() in m
    requires forall k:: 0 <= k < index ==> m[xs[k].StartAddress()] == k
    requires forall k:: k in m ==> m[k] < |xs| && xs[m[k]].StartAddress() == k
    ensures forall k:: 0 <= k < |xs| ==> xs[k].StartAddress() in r && r[xs[k].StartAddress()] == k
    ensures forall k:: k in r ==> r[k] < |xs| && xs[r[k]].StartAddress() == k
    decreases |xs| - index
  {
    if index == |xs| then m
    else
      CollectPCToSeg(xs, m[xs[index].StartAddress() := index], index + 1)
  }

}

