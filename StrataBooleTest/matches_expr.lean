/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

private def simple_matches : StrataDDM.Program :=
#strata
program Boole;


procedure match_pair_opt (p : pair int int, o : option int, o_none : option int)
spec{
  requires p == (1, 2);
  requires o == some(1);
  requires o_none == none<int>;
}
{
  assert (o matches some(v : int) && v == 1);
  assert (o_none matches none);
  assert (p matches (a : int, b : int) && (a == 1 && b == 2));
};

procedure match_wild (
  p : pair int bool,
  o : option int,
  dp : pair (pair int bool) (pair bool int)
)
spec{
  requires p == (2, true);
  requires o == some(1);
  requires dp == ((1, true), (false, 2));
}
{
  assert (p matches (_, b: bool) && b);
  assert (o matches some(_));
  assert (dp matches ((a: int, _), (_, b: int )) && a < b);
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

Obligation: assert_assert_3_380_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_3_380
Property: assert
Result: ✅ pass

Obligation: assert_4_426
Property: assert
Result: ✅ pass

Obligation: assert_5_458
Property: assert
Result: ✅ pass

Obligation: assert_9_737
Property: assert
Result: ✅ pass

Obligation: assert_10_777
Property: assert
Result: ✅ pass

Obligation: assert_11_807
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" simple_matches (options := .quiet)

private def matches_negative : StrataDDM.Program :=
#strata
program Boole;
procedure match_neg (
  p : pair int int,
  o : option int,
  o_none : option int,
  dp : pair (pair int bool) (pair bool int)
)
spec{
  requires p == (1, 2);
  requires o == some(1);
  requires o_none == none<int>;
  requires dp == ((1, true), (false, 2));
}
{
  assert (p matches (a : int, b : int) && b < a);
  assert (o matches some(v : int) && v == 2);
  assert (o matches none);
  assert (o_none matches some(v : int));
  assert (o_none matches some(_));
  assert (dp matches ((a: int, _), (_, b: int)) && a > b);
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

Obligation: assert_4_1930
Property: assert
Result: ❌ fail

Obligation: assert_assert_5_1980_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_5_1980
Property: assert
Result: ❌ fail

Obligation: assert_6_2026
Property: assert
Result: ❌ fail

Obligation: assert_7_2053
Property: assert
Result: ❌ fail

Obligation: assert_8_2094
Property: assert
Result: ❌ fail

Obligation: assert_9_2129
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" matches_negative (options := .quiet)


private def user_dt_match :=
#strata
program Boole;

datatype Triple (a : Type, b : Type, c : Type) {
  MkTriple(fst : a, snd : b, thd : c)
};

procedure user_dt_match (triple : Triple int int int)
spec{
  requires triple == MkTriple(2, 1, 3);
}
{
  assert (triple matches MkTriple(a : int, _, c : int) && a < c);
};

#end
/--
info:
Obligation: assert_1_3169
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" user_dt_match (options := .quiet)



/--
  Tests for precedence of matches (assumes longest match style rule when parsing)
  (@[prec(3)] expr:15 " matches " pattern " && " body:0;)

   - body:0 is greedy + result is prec(3) so below all other connectives
   -> matches has to be parenthesised when left of connective


  (@[prec(15)] expr " matches " pattern;)
   - above all connectives -> binds tighter than `<==>`,

-/
-- body is greedy so parses as o matches some(x) && (x > 0 ==> isSome(o)) : fail
private def greedy_body := #strata
program Boole;
procedure s1 (o : option int)
{
  assert o matches some(x : int) && x > 0 ==> isSome(o);
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

Obligation: assert_assert_0_3950_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_0_3950
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" greedy_body (options := .quiet)


-- Body spans `&&`: matches ∧ (c ∧ d), so `x` has to be instantiated : pass
private def greedy_body2 := #strata
program Boole;

procedure s2 (o : option int, d : bool)
spec{
  requires o == some(1);
}
{
  assert o matches some(x : int) && x > 0 && x < 2;
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

Obligation: assert_assert_1_4637_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_1_4637_calls_option..val_1
Property: assert
Result: ✅ pass

Obligation: assert_1_4637
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" greedy_body2 (options := .quiet)


-- `i + j` (prec 25) needs no parentheses : pass
private def add_parens := #strata
program Boole;
procedure s4 (i : int, j : int)
{
  assert i + j matches y : int && y == i + j;
};
#end
/--
info:
Obligation: assert_0_5333
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" add_parens (options := .quiet)


-- Bare form binds tighter than every connective.
private def fmt5 := #strata
program Boole;
procedure t5 (o : option int, d : bool) returns ()
{
  assert o matches some(_) <==> isSome(o);
  assert isNone(o) || o matches some(_);
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

Obligation: assert_0_5687
Property: assert
Result: ✅ pass

Obligation: assert_1_5730
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" fmt5 (options := .quiet)



#guard_msgs in
#eval Strata.Boole.verify "cvc5" simple_matches (options := .quiet)
