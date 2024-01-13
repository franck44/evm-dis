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
include "../utils/MiscTypes.dfy"
include "../utils/Instructions.dfy"
include "../proofobjectbuilder/SegmentBuilder.dfy"
include "../utils/Hex.dfy"
include "../utils/Statistics.dfy"
include "../utils/CFGState.dfy"

/**
  *  Provides pretty printers to HTML for Dot graphs and summaries.
  */
module HTML {

  import opened LinSegments
  import opened MiscTypes
  import opened Instructions
  import SegBuilder
  import Hex
  import opened Statistics
  import opened CFGState

  const INFO_SYMBOL := "&#8505;&#65039;" // a boxed grey i
  // Other options are: "&#8505;"; // "&#9636;"; // old symbol for stack of books is &#128218;
  const LARGER_OR_EQ_SYMBOL := "&#8805;"
  const DELTA_SYMBOL := "&#916;"
  const WHITE_SPACE_SYMBOL := "&#160;"
  const LINE_FEED_SYMBOL := "&#10;"

  /**
    *  A font tag. 
    */
  function Font(s: string, colour: string := ""): string
  {
    "<FONT" + (if colour != "" then  " COLOR=\"" + colour + "\"> " else "> ") + s + "</FONT>"
  }

  /**
    *  A table row tag.
    */
  function RowTR(s: string): string
  {
    "<TR>" + s + "</TR>\n"
  }

  /**
    * A table cell tag.
    */
  function CellTD(
    body: string,
    align: string := "left",
    fixedsize: bool := false,
    width: string := "",
    border: string  := "0",
    sides: string := "",
    colspan: string := "0",
    rowspan: string := "1",
    bgcolour: string := "",
    cellspacing: string := "0",
    cellpadding: string := "0",
    href: string := "",
    tooltip: string := ""): string
  {
    "<TD "
    + "ALIGN=\"" + align + "\" "
    + "fixedsize=\"" + (if fixedsize then "true" else "false") + "\" "
    + (if width != ""  then "WIDTH=\"" + width + "\" " else "")
    + "BORDER=\"" + border + "\" "
    + "SIDES=\"" + sides + "\" "
    + (if bgcolour != "" then "BGCOLOR=\"" + bgcolour + "\" " else "")
    + "CELLPADDING=\"" + cellpadding + "\" "
    + "CELLSPACING=\"" + cellspacing + "\" "
    + (if colspan != "0" then "COLSPAN=\"" + colspan + "\" " else "")
    + (if rowspan != "1" then "ROWSPAN=\"" + rowspan + "\" " else "")
    + "href=\"" + href + "\" "
    + (if tooltip != "" then "tooltip=\"" + tooltip + "\" " else "")
    + ">"
    + body
    + "</TD>\n"
  }

  /**
    * A table tag.
    */
  function Table(
    body: string,
    align : string := "left",
    colour: string := "black",
    bgcolour: string := "",
    cellborder: string := "0",
    border: string := "0",
    cellpadding: string := "0",
    cellspacing : string := "0"): string
  {
    "<TABLE "
    + "ALIGN=\"" + align + "\" "
    + "BORDER=\"" + border + "\" "
    + "CELLBORDER=\"" + cellborder + "\" "
    + "CELLPADDING=\"" + cellpadding + "\" "
    + "CELLSPACING=\"" + cellspacing + "\" "
    + (if bgcolour != "" then "BGCOLOR=\"" + bgcolour + "\" " else "")
    + "COLOR=\"" + colour + "\" "
    + ">"
    + body
    + "</TABLE>\n"
  }

  /**   Print the content of a segment. */
  function {:opaque} DOTSeg(s: ValidLinSeg, numSeg: nat, minStackSize: Option<nat>): (string, string)
  {
    //  Jump target
    var jumpTip :=
      if s.JUMPSeg? || s.JUMPISeg? then
        var r := SegBuilder.JUMPResolver(s);
        match r {
          case Left(v) =>
            match v {
              case Value(address) => LINE_FEED_SYMBOL + "Exit Jump target: Constant 0x" + Hex.NatToHex(address as nat)
              case Random(msg) => LINE_FEED_SYMBOL + "Exit Jump target: Unknown"
            }
          case Right(stackPos) => LINE_FEED_SYMBOL + "Exit Jump target: Stack on Entry.Peek(" + Int.NatToString(stackPos) +  ")"

        } else "";
    var stackSizeEffect := "Stack Size " + DELTA_SYMBOL + " : " + Int.IntToString(s.StackEffect());
    var minNumOpe := LINE_FEED_SYMBOL + "Stack Size on Entry for this segment " + LARGER_OR_EQ_SYMBOL + " " + Int.NatToString(s.WeakestPreOperands());
    var minNumOpAtNode :=  if minStackSize.Some? then LINE_FEED_SYMBOL + "Stack Size on Entry for this segment at this node " + LARGER_OR_EQ_SYMBOL + " " + Int.NatToString(minStackSize.v) else "";
    var prefix := "<B>Segment "
                  + Int.NatToString(numSeg)
                  + " [0x"
                  + Hex.NatToHex(s.StartAddress())
                  + "]</B><BR ALIGN=\"CENTER\"/>\n";
    var body := Instructions.ToDot(s.Ins());
    (prefix + body, stackSizeEffect +  jumpTip + minNumOpe + minNumOpAtNode)
  }

  /**
    *   Print content of a segment in a table with tooltips.
    */
  function DOTSegTable(s: ValidLinSeg, a: GState, minStackSize: Option<nat>): string
    requires a.EGState?
  {
    //  Jump target
    var jumpTip :=
      if s.JUMPSeg? || s.JUMPISeg? then
        var r := SegBuilder.JUMPResolver(s);
        match r {
          case Left(v) =>
            match v {
              case Value(address) =>  "Exit Jump target: Constant 0x" + Hex.NatToHex(address as nat)
              case Random(msg) =>  "Exit Jump target: Unknown"
            }
          case Right(stackPos) => "Exit Jump target: Stack on Entry.Peek(" + Int.NatToString(stackPos) +  ")"

        } else "";

    var gasSymbol := "&#9981; ";
    Table(
      cellspacing := "1",
      body :=
        RowTR(
          CellTD(
            "Segment " + Int.NatToString(a.segNum) + " [0x" + Hex.NatToHex(s.StartAddress()) + "]")
          + CellTD(
            body := Font(INFO_SYMBOL),
            tooltip :=
              "Stack Size " + DELTA_SYMBOL + ": " + Int.IntToString(s.StackEffect())
              + LINE_FEED_SYMBOL + "Abstract stack at this node: [" + a.StackToHTML() + "]"
              + (if minStackSize.Some? then LINE_FEED_SYMBOL + "Stack Size on Entry at this node " + LARGER_OR_EQ_SYMBOL + " " + Int.NatToString(minStackSize.v) else "")
              + LINE_FEED_SYMBOL + "Stack Size on Entry for this segment " + LARGER_OR_EQ_SYMBOL + " " + Int.NatToString(s.WeakestPreOperands())
              + (if jumpTip != "" then LINE_FEED_SYMBOL + jumpTip else "")
          )
          + CellTD(gasSymbol, tooltip := "lots of gas!")
        )
        + "<HR/>"
        + DOTInsTable(s.Ins())
    )
  }

  /**   Print a seq of instructions. */
  function DOTInsTable(xi: seq<Instructions.ValidInstruction>, isFirst: bool := true): string
  {
    if |xi| == 0 then ""
    else
      var prefix := "<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n";
      var suffix := "</TD></TR>\n";
      var exitPortTag := if xi[0].IsJump() then "PORT=\"exit\"" else "";
      var entryPortTag := if isFirst then "PORT=\"entry\"" else "";
      var a := xi[0].ToHTMLTable(entryPortTag, exitPortTag);
      (prefix + a + suffix) +  DOTInsTable(xi[1..], false)
  }

}

