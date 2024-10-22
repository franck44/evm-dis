/*
 * Copyright 2024 Franck Cassez
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

include "../../../src/dafny/disassembler/disassembler.dfy"
include "../../../src/dafny/proofobjectbuilder/Splitter.dfy"
include "../../../src/dafny/utils/EVMObject.dfy"

/**
  * Test correct computation of next State.
  * 
  */
module BuildCFGBlogTests {

  const debug:= false

  import opened OpcodeDecoder
  import opened EVMConstants
  import opened BinaryDecoder
  import opened Splitter
  import opened EVMObject

  //  Simple example. Two successive calls to same functions.
  method {:test} TestCFG1()
  {
    {
      var x := DisassembleU8(
        [
          /* 0x00: */ PUSH1, 0x05,
          /* 0x02: */ PUSH1, 0x0d,
          /* 0x04: */ JUMP,

          /* 0x05: */ JUMPDEST,
          /* 0x06: */ PUSH1, 0x0b,
          /* 0x08: */ PUSH1, 0x0d,
          /* 0x0a: */ JUMP,

          /* 0x0b: */ JUMPDEST,
          /* 0x0c: */ STOP,

          /* 0x0d: */ JUMPDEST,
          /* 0x0e: */ JUMP
        ]
      );

      expect |x| == 11;
      var y := SplitUpToTerminal(x);
      assert forall i, i' :: 0 <= i < i' < |y| ==> y[i].StartAddress() < y[i'].StartAddress();
      expect |y| == 4;
      expect y[0].StartAddress() == 0x00;
      var p: ValidEVMObj := EVMObj(y);
      var g, _ := p.BuildCFG(10, false) ;
      assert g.IsValid();
      expect g.SSize() == 5;
      expect g.TSize() == 4;
      if debug {
        print "CFG Test1\n";
        g.ToDot(nodeToString := (s, _) requires s in g.states => p.ToHTML(s),
                labelToString := (s, l, _) requires s in g.states && 0 <= l => p.DotLabel(s, l));
      }
    }
  }


  /**   A loop with growing stack.
    *  bytecode is 60025b5f908056
    */
  method {:test} {:verify true} Test5()
  {
    //  Linear segment
    var x := DisassembleU8(
      [
        // Segment 0
        /* 00000000: */ PUSH1, 0x02,
        //  Segment 1
        /* 00000002: */ JUMPDEST,
        /* 00000003  */ PUSH0,
        SWAP1,
        /* 00000004: */ DUP1,
        /* 00000005: */ JUMP

      ]);

    expect |x| == 6;
    var y := SplitUpToTerminal(x);
    assert forall i, i' :: 0 <= i < i' < |y| ==> y[i].StartAddress() < y[i'].StartAddress();

    expect |y| == 2;
    expect y[1].StartAddress() == 0x02;
    expect y[0].StartAddress() == 0;

    var p := EVMObj(y);
    var g, _ := p.BuildCFG(10) ;
    assert g.IsValid();
    expect g.SSize() == 2;
    expect g.TSize() == 2;
    if debug {
      print "CFG Test1\n";
      g.ToDot(nodeToString := (s, _) requires s in g.states => p.ToHTML(s),
              labelToString := (s, l, _) requires s in g.states && 0 <= l => p.DotLabel(s, l));
    }
  }

  /** max-max. */
  method {:test} {:verify false} Test6()
  {
    var x := Disassemble("60126008600e6003600a92601b565b601b565b60405260206040f35b91908083106027575b50565b909150905f602456");
    var y := SplitUpToTerminal(x);
    assert forall i, i' :: 0 <= i < i' < |y| ==> y[i].StartAddress() < y[i'].StartAddress();

    var p := EVMObj(y);
    var g, _ := p.BuildCFG(10) ;
    assert g.IsValid();
    expect g.SSize() == 9;
    expect g.TSize() == 10;
    if debug {
      print "CFG Test1\n";
      g.ToDot(nodeToString := (s, _) requires s in g.states => p.ToHTML(s),
              labelToString := (s, l, _) requires s in g.states && 0 <= l => p.DotLabel(s, l));
    }
  }
}

