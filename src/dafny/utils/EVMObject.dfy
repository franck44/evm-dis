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
include "../utils/MinimiserAState.dfy"
include "../CFGBuilder/BuildCFGSimplified.dfy"

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
  import Automata
  import opened DFSSimple
  import opened PartitionMod
  import opened AStateMinimiser
  import opened WeakPre
  import opened StackElement

  /**
    *    A valid sequence of valid linear segments. To be valid the sequence 
    *    must be ordered by start addresses.
    */
  type ValidSeqValidLinSeg = xs: seq<ValidLinSeg> | forall i, i':: 0 <= i < i' < |xs| ==> xs[i].StartAddress() < xs[i'].StartAddress()

  /**   A valid EVMObj should have a PCToSegMap that is the reverse of xs -> startAddress() . */
  type ValidEVMObj = e: EVMObj | e.IsValid() witness EVMObj([], [])

  /**   An EVMObj has segments and jumpDests. */
  datatype EVMObj = EVMObj(
    xs: ValidSeqValidLinSeg,
    jumpDests: seq<nat> := CollectJumpDests(xs),
    startAddresses: seq<nat> := CollectStartAddresses(xs),
    PCToSegMap: map<nat, nat> := CollectThem(xs)
    // PCToSegMap: map<nat, nat> := CollectPCToSeg(xs) . does not work with VsCode plugin ...hangs up
  ) {

    /** A valid EVMObj has jumpDests consistent with xs. */
    predicate IsValid() {
      && (forall i, i':: 0 <= i < i' < |xs| ==> xs[i].StartAddress() < xs[i'].StartAddress())
      && (forall k:: k in PCToSegMap ==> PCToSegMap[k] < |xs| && xs[PCToSegMap[k]].StartAddress() == k)
    }

    /** The size of the program in bytes. */
    function Size(ls: seq<ValidLinSeg> := xs): nat {
      if |ls| == 0 then 0
      else ls[0].Size() + Size(ls[1..])
    }

    // lemma foo101(s: ValidLinSeg, c:seq<nat>)
    //   requires |c| <= s.NumberOfExits()
    //   ensures forall k {:nowarn}:: 0 <= k < |c| ==> k < s.NumberOfExits()
    //   ensures forall k:: 0 <= k < |c| ==> s.IsValidExit(k)
    // {   //  Thanks Dafny
    // }

    /**
      * Compute the next abstract states from a given abstract state.
      * @param s The abstract state.
      * @returns The next abstract states.
      *
      * @note   This function is _inductive_ in the sense of the Inductive predicate (see BuildCFG).
      */
    function {:opaque} NextG(s: GState): (r: seq<GState>)
      requires this.IsValid()
      requires s.EGState? ==> s.segNum < |xs|
      ensures forall k:: 0 <= k < |r| && r[k].EGState? ==> r[k].segNum < |xs|
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
      else match PCToSeg(s.pc)
           case Some(seg) =>
             if xs[seg].NumberOfExits() > exits[0] then
               foo(xs[seg], exits[0]);
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
           case None => Error("No segment found for state " + s.ToString())

    }

    /**
      *   Whether a condition is invariant under a given path.
      *   @param  c           A condition.
      *   @param  exits       The exit after each segment.
      */
    predicate {:opaque} PreservesCond(c: ValidCond, exits: seq<nat>)
      requires this.IsValid()
      requires c.StCond?
    {
      var initState := BuildInitState(c);
      var endState := RunAll(exits, initState);
      if endState.EState? then
        endState.Sat(c)
      else false
    }

    /**
      *   Check if a state whit this pc has been seen before, and whether we can loop back 
      *   to an already seen state on this path.
      *
      *   @note   The seenOnPath has all the nodes seen before the current one.
      *           The current one has startAddress == pc.
      */
    // function SafeLoopFound(pc: nat, seenOnPath: seq<AState>, exits: seq<nat>): (r: Option<AState>)
    //   requires this.IsValid()
    //   requires |xs| >= 1
    //   requires pc < Int.TWO_256
    //   requires 0 < |seenOnPath| // == |path|
    //   requires |exits| == |seenOnPath|
    //   requires forall k :: 0 <= k < |seenOnPath| ==> seenOnPath[k].EState? && PCToSeg(seenOnPath[k].pc).Some?
    //   // requires forall k:: k in seenOnPath ==> k.seg.Some? && k.seg.v < |xs|
    //   // requires xs[seenOnPath[|seenOnPath| - 1].seg.v].JUMPSeg? || xs[seenOnPath[|seenOnPath| - 1].seg.v].JUMPISeg?
    //   // ensures r.Some? ==> r.v.seg.Some? && r.v.seg.v < |xs|
    //   decreases |seenOnPath|
    // {
    //   match FindFirstNodeWithPC(pc, seenOnPath)
    //   case Some(v) =>
    //     //  pc occurs on this path and v is an abstract state s with s.pc == pc
    //     assert v.0.EState?;
    //     assert v.0.pc == pc;
    //     //  some properties must hold on the path defined by the index v.1
    //     var init := seenOnPath[v.1];
    //     //  the CFGMNode at index v.1 has a segment with start address == pc
    //     //   assert xs[init.seg.v].StartAddress() == pc;
    //     //  get the path false|true that led from init to last node
    //     var path := seenOnPath[v.1..];
    //     //   //  compute the list of segments defined by the nodes in path
    //     //   var segs := NodesToSeg(path);
    //     assert forall k :: 0 <= k < |path| ==> path[k].EState? && PCToSeg(path[k].pc).Some?;
    //     var segs := seq(|path|, i requires 0 <= i < |path| => PCToSeg(path[i].pc).v);
    //     //  compute the Wpre for last node path to lead to pc (via true)
    //     assert pc < Int.TWO_256;
    //     assume xs[PCToSeg(seenOnPath[|seenOnPath| - 1].pc).v].IsValidExit(exits[|exits| - 1]);
    //     var tgtCond := xs[PCToSeg(seenOnPath[|seenOnPath| - 1].pc).v].LeadsTo(pc, exits[|exits| - 1]);
    //     //    Compute the WPre for for segments in path
    //     var w1 := WPreSeqSegs(segs, exits[v.1..], tgtCond, xs, pc);
    //     //   if w1.StTrue? then
    //     //     Some(v.0)
    //     //   else if w1.StFalse? then
    //     //     None
    //     //   else if PreservesCond(w1, segs, boolPath[v.1..], xs, jumpDests) then
    //     //     Some(v.0)
    //     //   //  Try a potential second occurrence of pc om seenOnPath
    //     //   else if 0 < |seenOnPath[v.1..|seenOnPath|]| < |seenOnPath| then
    //     //     SafeLoopFound(xs, pc, seenOnPath[v.1..|seenOnPath|], boolPath[v.1..|boolPath|], jumpDests)
    //     //   else None
    //     None

    //   case None =>
    //     //  No occurrence of pc on this path
    //     None
    // }

    /**
      *   Find the first node in a sequence with a givem value for pc.
      *   @param  pc      The pc to find in s.
      *   @param  s       A sequence of states.
      *   @param  index   The current index in the search.
      *   @returns        The node, index of the first occurrence of a state in s with 
      *                   s.pc equals to pc. 
      */
    // function FindFirstNodeWithPC(pc: nat, s: seq<AState>, index: nat := 0): (r: Option<(AState, nat)>)
    //   requires index <= |s|
    //   ensures r.Some? ==> r.v.0.EState?
    //   ensures r.Some? ==> r.v.1 < |s|
    //   ensures r.Some? ==> s[r.v.1].EState?
    //   ensures r.Some? ==> s[r.v.1].pc == pc == r.v.0.pc
    //   decreases |s| - index
    // {
    //   if |s| == index then None
    //   else
    //     match s[index]
    //     case EState(pc', st) =>
    //       if pc' == pc then Some((s[index], index))
    //       else FindFirstNodeWithPC(pc, s, index + 1)
    //     case Error(m) => None
    // }

    /**
      * Build the CFG of the EVMObj.
      * The CFG is built by running a DFS from the initial state.
      * @param maxDepth The maximum depth of the DFS.
      * @param minimise If true, the CFG is minimised.   
      */
    method {:opaque} BuildCFG(maxDepth: nat := 100, minimise: bool := true) returns (a: Automata.ValidAuto<GState>)
      requires this.IsValid()
      requires |xs| >= 1
      ensures forall s:: s in a.states && s.EGState? ==> s.segNum < |xs|
    {
      //  For now we ignore the history
      var a1, _ := DFS(
        NextG,
        // DEFAULT_VALIDSTATE,
        DEFAULT_GSTATE,
        History(DEFAULT_GSTATE, [DEFAULT_GSTATE]),
        Automata.Auto(),
        maxDepth);
      if !minimise || a1.SSize() == 0 {
        return a1;
      } else {
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

        var vp: AStateMinimiser.Pair := Pair(a1, p2);
        var a2 := vp.Minimise();
        return a2;
      }

    }

    // lemma foo303()
    //   requires this.IsValid()
    //   requires |xs| >= 1
    //   ensures NextG.requires(DEFAULT_GSTATE)
    // { assert NextG.requires(DEFAULT_GSTATE); }

    /**
      * Generate the HTML representation of a given abstract state.
      */
    function ToHTML(a: GState): string
      requires this.IsValid()
      requires a.EGState? ==> a.segNum < |xs|
    {
      if a.ErrorGState? then
        "<ErrorEnd <BR ALIGN=\"CENTER\"/>>"
      else
        //  because of the pre-condition, we are sure that a has a segNum < |xs|
        //  and we can use xs[a.segNum]
        "<" + DOTSeg(xs[a.segNum], a.segNum).0 +">"
    }

    /**
      *   Retrieve num of segment that correspond to a PC if any.
      */
    // function PCToSeg(pc: nat, rank: nat := 0): (r: Option<nat>)
    //   requires this.IsValid()
    //   requires rank <= |xs|
    //   ensures r.Some? ==> r.v < |xs|
    //   ensures r.Some?  ==> xs[r.v].StartAddress() == pc
    //   //   ensures pc in startAddresses ==> r.Some?
    //   decreases |xs| - rank
    // {
    //   if rank == |xs| then None
    //   else if xs[rank].StartAddress() == pc then Some(rank)
    //   else PCToSeg(pc, rank + 1)
    // }

    function {:opaque} PCToSeg(pc: nat): (r: Option<nat>)
      requires this.IsValid()
      ensures r.Some? ==> r.v < |xs| && xs[r.v].StartAddress() == pc
    {
      if pc in PCToSegMap then
        Some(PCToSegMap[pc])
      else
        None
    }

    // function CollectStartAddressOfSegs(): (r: seq<nat>)
    //   ensures |xs| == |r|
    // {
    //   CollectStartAddresses(xs)
    // }

    // function CollectStartAddressesV2(index: nat := 0, m: map<nat, nat> := map[]): (r: map<nat, nat>)
    //   requires index <= |xs|
    //   requires |m| <= index <= |xs|
    //   requires forall i:: 0 <= i < |m| ==> m[i] == xs[i].StartAddress()
    //   ensures |r| <= |xs|
    //   ensures forall i:: 0 <= i < |r| ==> r[i] == xs[i].StartAddress()
    //   decreases |xs| - index
    // {
    //   if index == |xs| then m
    //   else
    //     // map[xs[index].StartAddress() := index] +
    //     CollectStartAddressesV2(index + 1, m[xs[index].StartAddress() := index] )
    // }

    // lemma foo101(pc: nat)
    //     requires pc in CollectStartAddressOfSegs()
    //     // ensures PCToSeg(pc).Some?
    // {
    //     var k1 :| k1 in CollectStartAddressOfSegs() && k1 == pc;
    //     var k :| 0 <= k < |CollectStartAddressOfSegs()| && CollectStartAddressOfSegs()[k] == pc;
    //     assert 0 <= k < |xs|;
    //     assert xs[k].StartAddress() == pc;
    //     assert PCToSeg(pc).Some?;
    // }


  }

  /**   Print the content of a segment. */
  function DOTSeg(s: ValidLinSeg, numSeg: nat): (string, string)
  {
    //  Jump target
    var jumpTip :=
      if s.JUMPSeg? || s.JUMPISeg? then
        var r := SegBuilder.JUMPResolver(s);
        match r {
          case Left(v) =>
            match v {
              case Value(address) => "&#10;Exit Jump target: Constant 0x" + Hex.NatToHex(address as nat)
              case Random(msg) => "&#10;Exit Jump target: Unknown"
            }
          case Right(stackPos) => "&#10;Exit Jump target: Stack on Entry.Peek(" + Int.NatToString(stackPos) +  ")"

        } else "";
    var stackSizeEffect := "Stack Size &#916;: " + Int.IntToString(s.StackEffect());
    var mninNumOpe := "&#10;Stack Size on Entry &#8805; " + Int.NatToString(s.WeakestPreOperands());
    var prefix := "<B>Segment "
                  + Int.NatToString(numSeg)
                  + " [0x"
                  + Hex.NatToHex(s.StartAddress())
                  + "]</B><BR ALIGN=\"CENTER\"/>\n";
    var body := Instructions.ToDot(s.Ins());
    (prefix + body, stackSizeEffect +  jumpTip + mninNumOpe)
  }

  /** Collect jumpdests in a list of segments.  */
  function {:opaque} CollectJumpDests(xs: seq<ValidLinSeg>): seq<nat> {
    if |xs| == 0 then []
    else
      xs[0].CollectJumpDest() + CollectJumpDests(xs[1..])
  }

  function {:opaque} CollectStartAddresses(segs: seq<ValidLinSeg>): (r: seq<nat>)
    ensures |segs| == |r|
    ensures forall i:: 0 <= i < |r| ==> r[i] == segs[i].StartAddress()
  {
    if |segs| == 0 then []
    else
      [segs[0].StartAddress()] + CollectStartAddresses(segs[1..])
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
    *  @param  m       The map that has been built so far. 
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

