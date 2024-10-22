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

include "./MiscTypes.dfy"
include "./int.dfy"

/** Provide parsing of commadline options. 
  * 
  * Usage: see at the end of the module for an example method.
  */
module ArgParser {

  import opened MiscTypes
  import Int

  /**
    *   An option.
    *   @param  name    The name of the option. The is used to retrieve the value of
    *                   of an option on the command line.
    *   @param  numArgs The number of expected arguments for the option.
    *   @param  desc    The text description for the option (help).
    */
  datatype CLIOption = CLIOption(name: string, numArgs: nat, desc: string)

  /**
    *   Provides argument parser.
    */
  class ArgumentParser {


    /** The list of known options.
      * Argument name, and number of expected arguments/help for the option.
      */
    var knownArgs: map<string, CLIOption>
    /** The long name. e.g. "--file" associated with a short name e.g. "-f". */
    var knownNameArgs: map<string, string>

    /** The list of known keys. Useful to iterate over keys in a map. */
    var knownKeys: seq<string>

    ghost var registeredOptions: set<string>

    var usageSuffix: string

    /**
      *  Ensure the list of keys is the same as the list of knownArgs keys.
      */
    ghost predicate Inv()
      reads this
    {
      && multiset(knownArgs.Keys) == multiset(knownKeys)
      && knownArgs.Keys + knownNameArgs.Keys == registeredOptions
         //   && (forall k:: k in registeredOptions ==> Canonical(k) in knownArgs.Keys)
    }

    /**
      * Initialise the args.
      */
    constructor(s: string := "")
      ensures Inv()
      ensures (forall k:: k in registeredOptions ==> Canonical(k) in knownArgs.Keys)
      ensures knownArgs.Keys == { "--help" }
    {
      usageSuffix := s ;
      knownArgs := map["--help" := CLIOption("-h", 0, "Display help and exit")];
      knownNameArgs := map["-h" := "--help"];
      knownKeys := ["--help"];

      registeredOptions := { "--help", "-h" };
    }

    /**
      * Register a new option.
      * 
      * @param  opname  The short name of the option, e.g. "-h" or "-a"
      * @param  name    The longname of the option, e.g. "--help" or "--file"
      * @param  numArgs The number of arguments that the option takes. E.g. if "--file" should
      *                 be followed by one argument, it is 1. Default value is 0.
      * @param  help    The description of the option.
      *
      * @note   If the option name already exists, it is overriden.
      */
    method {:verify true} AddOption(opname: string, name: string, numArgs: nat := 0, help: string := "No help provided")
      requires Inv()
      requires name !in knownArgs.Keys
      ensures Inv()
      ensures old(knownArgs.Keys) <= knownArgs.Keys
      ensures  knownArgs.Keys == old(knownArgs.Keys) + { name }
      ensures forall k:: k in old(knownArgs.Keys) ==> k in knownArgs.Keys && knownArgs[k] == old(knownArgs[k])
      ensures name in knownArgs.Keys && knownArgs[name].numArgs == numArgs
      modifies `knownArgs, `knownKeys, `knownNameArgs, `registeredOptions
    {
      knownArgs := knownArgs[name := CLIOption(opname, numArgs, help)];
      knownNameArgs := knownNameArgs[opname := name];
      if name !in knownKeys {
        knownKeys := knownKeys + [name];
      }
      registeredOptions := registeredOptions + {opname, name};
    }

    /**
      *  Print out the help of options and the number of arguments and help.
      */
    method {:verify true} PrintHelp()
      requires Inv()
      ensures Inv()
    {
      print "usage: <this program> ";
      for i := 0 to |knownKeys| {
        assert knownKeys[i] in multiset(knownKeys);
        var k := knownArgs[knownKeys[i]];
        print " [", knownKeys[i], "] ";
        //  print arguments
        for i := 0 to k.numArgs {
          print  " arg", i;
        }
      }
      print " ", usageSuffix;
      print "\n\n";
      //    Display option help one per line
      print "options", "\n";
      var maxL := MaxValueFast(knownKeys);

      for i := 0 to |knownKeys| {
        assert knownKeys[i] in multiset(knownKeys);
        var k := knownArgs[knownKeys[i]];
        SameMax(knownKeys);
        print knownKeys[i], seq(maxL - |knownKeys[i]| + 2, _ => ' ') , " [", k.name, "] ", k.desc ;
        print "\n";
      }
    }

    //
    function GetArgs(key: string, s: seq<string>) : (r: Try<seq<string>>)
      requires Inv()
      ensures Inv()
      ensures r.Success? ==> key in knownArgs.Keys && |r.v| == knownArgs[key].numArgs
      reads this
    {
      if |s| == 0 then Failure("Not found")
      else if key !in knownArgs.Keys then Failure("Not a key")
      else
      if Canonical(s[0]) == key then
        var opt: CLIOption := knownArgs[key];
        var numArgs := opt.numArgs;
        if |s[1..]| < numArgs then
          Failure("argument " + s[0] + " needs more arguments")
        else
          //   read them
          Success(s[1..][..numArgs])
      else
        GetArgs(key, s[1..])
    }

    /**
      *  Expand short names ot canonical.
      */
    function Canonical(s: string): string
      reads `knownNameArgs
    {
      if s in knownNameArgs then knownNameArgs[s]
      else s
    }

    //  Helpers and Lemmas

    /**
      *  Max length of elements in the sequence.
      */
    ghost function MaxValue(s: seq<string>): (r: nat)
      ensures forall i:: 0 <= i < |s| ==> |s[i]| <= r
    {
      if |s| == 0 then 0
      else Int.Max(|s[0]|, MaxValue(s[1..]))
    }

    /**
      * Tail recursive computation of max value.
      */
    function {:tailrecursion true} MaxValueFast(s: seq<string>, max: nat := 0): (r: nat)
    {
      if |s| == 0 then max
      else MaxValueFast(s[1..], Int.Max(|s[0]|, max))
    }

    //  Some useful lemmas

    lemma SameMax(s: seq<string>)
      ensures MaxValue(s) == MaxValueFast(s, 0)
      ensures forall i:: 0 <= i < |s| ==> |s[i]| <= MaxValueFast(s)
    {
      if |s| > 0 {
        SameMaxExtractFirst(s[1..], s[0]);
      }
    }

    lemma SameMaxExtractFirst(s: seq<string>, e: string)
      ensures MaxValue([e] + s) == MaxValueFast(s, |e|)
    {
      //  Thanks Dafny
    }
  }

  method {:test} Main() {
    print "hello! Testing ArgParser!\n";
    var cli := new ArgumentParser("<filename>");
    cli.AddOption("-o", "--one");
    cli.AddOption("-tw", "--two", 2, "don't do that!");

    var r := ["-one", "--two", "a1", "a2", "-unknwon"];

    match cli.GetArgs("-o", r) {
      case Success(a) => print "Success -o! has arguments:", a, "\n" ;

      case Failure(m) =>  print "No -o! ", "\n" ;
    }

    match cli.GetArgs("--two", r) {
      case Success(a) => print "Success -two! has arguments: ", a, "\n" ;

      case Failure(m) =>  print "No --two! ", "\n" ;
    }

    cli.PrintHelp();
  }


}