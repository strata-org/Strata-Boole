/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

private def simple_matches : StrataDDM.Program :=

#strata

program Boole;

datatype Triple (a : Type, b : Type, c : Type) {
  MkTriple(fst : a, snd : b, thd : c)
};

procedure match_var () returns ()
{
  var p : Pair int bool := (2, true);
  assert (p matches (_, b: bool) && b == true);

  var opt : option int := some(1);
  assert (opt matches some(_) && true);
  assert (opt matches some(v : int) && v == 1);
  assert (opt matches some(v : int) && v == 2);                            // should fail

  var p2 : Pair int int := (1, 2);
  assert (p2 matches (a : int , b : int) && (a == 1 && b == 2));
  assert (p2 matches (a : int, b : int) && b < a);                         //should fail

  var o : option (Pair bool int) := some((true, 12));
  assert (o matches some((_, a : int)) && a == 12);

  var double_pair : Pair (Pair int bool) (Pair bool int) := ((1, true), (false, 2));
  assert (double_pair matches ((a: int, _), (_, b: int )) && a < b);
  assert (double_pair matches ((a: int, _), (_, b: int)) && a > b);       // should fail

  var t : Triple int bool int := MkTriple(1, true, 3);
  //assert (t matches MkTriple(a : int, b: bool, c : int) && a < c);

};


#end

#eval Strata.Boole.verify "cvc5" simple_matches (options := .debug)
