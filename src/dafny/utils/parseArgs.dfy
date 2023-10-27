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

/** Provide parsing of commadline optios. */
module parseArgs {

  class Args {

    /** The list of known options.
      * Argument name, and number of expected arguments for the option.
      */
    var knownArgs: map<string, nat>

    /** The list of known keys. Useful to iterate over keys in a map. */
    var knownKeys: seq<string>

    /**
     *  Ensure the list of keys is the same as the list of knownArgs keys.
     */
    ghost predicate Inv()
      reads this
    {
      multiset(knownArgs.Keys) == multiset(knownKeys)
    }

    constructor()
      ensures Inv()
    {
      knownArgs := map[];
      knownKeys := [];
    }

    method {:verify true} AddOption(name: string, numArgs: nat := 0, help: string := "No help")
      requires Inv()
      modifies `knownArgs, `knownKeys
      ensures Inv()
    {
      knownArgs := knownArgs[name := numArgs];
      if name !in knownKeys {
        knownKeys := knownKeys + [name];
      }

    }

    method {:verify true} Print()
      requires Inv()
      ensures Inv()
    {
      for i := 0 to |knownKeys| {
        assert knownKeys[i] in multiset(knownKeys);
        print knownKeys[i], " ", knownArgs[knownKeys[i]];
      }
    }
  }

  method {:main} Main() {
    print "hello\n";
    var cli := new Args();
    cli.AddOption("-one");

    cli.Print();
    print "\n";
    print cli.knownKeys, "\n";

  }


}