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

procedure match_pair () returns ()
{
  var p2 : pair int int := (1, 2);
  assert (p2 matches (a : int , b : int) && (a == 1 && b == 2));
  assert (p2 matches (a : int, b : int) && b < a);                    // should fail
};

procedure match_opt () returns ()
{
  var opt : option int := some(1);
  assert (opt matches some(v : int) && v == 1);
  assert (opt matches some(v : int) && v == 2);                            // should fail
};

procedure match_wild () returns (){
  // matches in pair
  var p : pair int bool := (2, true);
  assert (p matches (_, b: bool) && b);

  // matches in some constructor
  var o : option int := some(1);
  var o_none : option int := none<int>;
  assert (o matches some(_) && true);
  assert (o_none matches none && true);
  assert (o matches none && true);                                        // should fail

  // nested matches
  var double_pair : pair (pair int bool) (pair bool int) := ((1, true), (false, 2));
  assert (double_pair matches ((a: int, _), (_, b: int )) && a < b);
  assert (double_pair matches ((a: int, _), (_, b: int)) && a > b);       // should fail

  // matches in user supplied constructor
  var t : Triple int bool int := MkTriple(1, true, 3);
  assert (t matches MkTriple(a : int, _, c : int) && a < c);
};


#end

/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_0_372
Property: assert
Result: ✅ pass

Obligation: assert_1_437
Property: assert
Result: ❌ fail

Obligation: assert_2_597
Property: assert
Result: ✅ pass

Obligation: assert_3_645
Property: assert
Result: ❌ fail

Obligation: assert_4_834
Property: assert
Result: ✅ pass

Obligation: assert_5_981
Property: assert
Result: ✅ pass

Obligation: assert_6_1019
Property: assert
Result: ✅ pass

Obligation: assert_7_1059
Property: assert
Result: ❌ fail

Obligation: assert_8_1254
Property: assert
Result: ✅ pass

Obligation: assert_9_1323
Property: assert
Result: ❌ fail

Obligation: assert_10_1510
Property: assert
Result: ✅ pass
-/

#guard_msgs in
#eval Strata.Boole.verify "cvc5" simple_matches (options := .quiet)
