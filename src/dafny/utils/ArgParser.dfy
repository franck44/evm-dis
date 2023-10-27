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
    var knownNameArgs: map<string, string>

    /** The list of known keys. Useful to iterate over keys in a map. */
    var knownKeys: seq<string>

    var usageSuffix: string

    /**
      *  Ensure the list of keys is the same as the list of knownArgs keys.
      */
    ghost predicate Inv()
      reads this
    {
      && multiset(knownArgs.Keys) == multiset(knownKeys)
      && knownNameArgs.Values <= knownArgs.Keys
    }

    /**
      * Initialise the args.
      */
    constructor(s: string := "")
      ensures Inv()
    {
      usageSuffix := s ;
      knownArgs := map["-h" := CLIOption("--help", 0, "Display help and exit")];
      knownNameArgs := map["--help" := "-h"];
      knownKeys := ["-h"];
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
      modifies `knownArgs, `knownKeys, `knownNameArgs
      ensures Inv()
    {
      knownArgs := knownArgs[opname := CLIOption(name, numArgs, help)];
      knownNameArgs := knownNameArgs[name := opname];
      if opname !in knownKeys {
        knownKeys := knownKeys + [opname];
      }
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
        print knownKeys[i], seq(maxL - |knownKeys[i]| + 2, _ => ' ') , " [", k.name, "] ", k.desc ; // , " ", k.0;
        print "\n";
      }
    }

    /**
      * Parse the commandline arguments and collect options' values.
      *
      * @param  args            The arguments to be parsed.
      * @param  alreadyParsed   The already collected option values.
      * @returns                A Success with a map, mapping option long names with their
      *                         list of arguments or Failure is parsing fails.
      *                         If it succeeds, the map contains the entries that correspond
      *                         to options in the command line arguments.
      *                         The key to the option is the long name, e.g. for am option "-f" with
      *                         longname "--file", the entry for "-f" or "--file" will be at "--file".
      * @example                if "--file" is declared with 1 argument, parsing "--file" filename
      *                         succeeds. If ""-file" is not followed by one argument, it fails.
      * @example                Note that "--file" "--quiet" will succeed and interpret "--quiet" as 
      *                         the argument of "--file".
      */
    function ParseArgs(args: seq<string>, alreadyParsed: map<string, seq<string>> := map[]): Try<map<string, seq<string>>>
      reads this
      requires Inv()
      ensures Inv()
    {
      //  parse the seq and retrieve the values of known options.
      if |args| == 0 then Success(alreadyParsed)
      else
      if args[0] in knownArgs.Keys || args[0] in knownNameArgs.Keys then
        //  read the number of arguments if possible, and otherwise
        //  fail.
        // Retrieve option
        var opt := if args[0] in knownArgs.Keys then knownArgs[args[0]]
                   else knownArgs[knownNameArgs[args[0]]];
        var numArgs := opt.numArgs;
        if |args[1..]| < numArgs then
          Failure("argument " + args[0] + " needs more arguments")
        else
          //   read them
          var r := args[1..][..numArgs];
          ParseArgs(args[1 + numArgs..], alreadyParsed[opt.name := r])

      else 
        ParseArgs(args[1..], alreadyParsed)
    }

    //  Helper

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
    print "hello! Testing parseArg!\n";
    var cli := new ArgumentParser("<filename>");
    cli.AddOption("-o", "--one");
    cli.AddOption("-tw", "--two", 2, "don't do that!");

    var r := cli.ParseArgs(["-one", "--two", "a1", "a2", "-unknwon"]);

    match r {
      case Success(m) =>
        if "-o" in m.Keys {
          print "Success -o!", m["-o"], "\n" ;
        }
        if "--two" in m.Keys {
          print "Success -two!", m["--two"], "\n" ;
        }
      case Failure(msg) =>
        print msg, "\n";

    }
    cli.PrintHelp();
  }


}