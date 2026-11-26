/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
# Pattern matching conditions
covers positive matches, intentional failures, nested patterns, user datatypes, quantifiers,
precedence, and Lean VC generation for a non-generic datatype.

TODO:
  - Lean verification condition generation path for parameterized option/pair
-/

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
  dp : pair (pair int bool) (pair bool int),
  op : option (pair int int)
)
spec{
  requires p == (2, true);
  requires o == some(1);
  requires dp == ((1, true), (false, 2));
  requires op == some((1, 2));
}
{
  assert (p matches (_, b: bool) && b);
  assert (o matches some(_));
  assert (dp matches ((a: int, _), (_, b: int )) && a < b);
  assert (op matches some((_, a: int)) && a == 2);
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

Obligation: assert_assert_3_658_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_3_658
Property: assert
Result: ✅ pass

Obligation: assert_4_704
Property: assert
Result: ✅ pass

Obligation: assert_5_736
Property: assert
Result: ✅ pass

Obligation: assert_10_1076
Property: assert
Result: ✅ pass

Obligation: assert_11_1116
Property: assert
Result: ✅ pass

Obligation: assert_12_1146
Property: assert
Result: ✅ pass

Obligation: assert_assert_13_1206_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_13_1206
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

Obligation: assert_4_2475
Property: assert
Result: ❌ fail

Obligation: assert_assert_5_2525_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_5_2525
Property: assert
Result: ❌ fail

Obligation: assert_6_2571
Property: assert
Result: ❌ fail

Obligation: assert_7_2598
Property: assert
Result: ❌ fail

Obligation: assert_8_2639
Property: assert
Result: ❌ fail

Obligation: assert_9_2674
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
Obligation: assert_1_3714
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" user_dt_match (options := .quiet)



/--
  Tests for precedence of matches
  (@[prec(15)] expr:15 " matches " pattern " && " body:9;)
  (@[prec(15)] expr:15 " matches " pattern " ==> " body:4;)

  - scoped `&&` guard parses at same precedence as a conjunction:
   an unparenthesized `||` is outside the match.
   Parentheses put it inside the body so pattern variables are in scope.

  - && condition accepts && at precedence 10 but stops before || at 8 and ==> at 5,
   the implication condition at 4 can include a ==> chain.

  (@[prec(15)] expr " matches " pattern;)
   - above all connectives -> binds tighter than `<==>`,

-/
private def matches_or_precedence := #strata
program Boole;
procedure matches_or_precedence (o : option int, b : bool, o2 : option int)
spec{
  requires o == none<int>;
  requires o2 == some(0);
  requires b;
}
{
  assert o matches some(x : int) && x > 0 || b;
  assert !(o matches some(x : int) && (x > 0 || b));
  assert o2 matches some(x : int) && (x > 0 || b);
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

Obligation: assert_assert_3_4754_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_3_4754
Property: assert
Result: ✅ pass

Obligation: assert_assert_4_4802_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_4_4802
Property: assert
Result: ✅ pass

Obligation: assert_assert_5_4855_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_5_4855
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" matches_or_precedence (options := .quiet)

private def matches_chain := #strata
program Boole;
procedure matches_chain (o : option int, b : bool, n : option int)
spec{
  requires o == some(1);
  requires b;
  requires n == none<int>;
}
{
  assert o matches some(x : int) && x > 0 && x < 2;
  assert n matches some(x : int) ==> true ==> false;
  assert n matches some(x : int) && x > 0 ==> b;
  assert !(n matches some(x : int) && (x > 0 ==> b));
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

Obligation: assert_assert_3_5831_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_3_5831_calls_option..val_1
Property: assert
Result: ✅ pass

Obligation: assert_3_5831
Property: assert
Result: ✅ pass

Obligation: assert_4_5883
Property: assert
Result: ✅ pass

Obligation: assert_assert_5_5936_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_5_5936
Property: assert
Result: ✅ pass

Obligation: assert_assert_6_5985_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_6_5985
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" matches_chain (options := .quiet)


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
Obligation: assert_0_7043
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

Obligation: assert_0_7397
Property: assert
Result: ✅ pass

Obligation: assert_1_7440
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" fmt5 (options := .quiet)


/--
  Test for solver timeout and binders fix
-/
private def quantified_matches := #strata
program Boole;
procedure match_quantified (o : option int)
spec{
  requires o == some(1);
}
{
  assert ∃ y : int . (o matches some(x : int) && x == y);
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

Obligation: assert_assert_1_8055_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_1_8055
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" quantified_matches (options := .quiet)


/-
  Test for Lean VC generation with a Core datatype
-/
private def testvc := #strata
program Boole;
procedure match_quantified (s : Sequence int)
{
  assert s matches s : Sequence int && Sequence.length(s) >= 0;
};

#end
/--
info:
Obligation: assert_0_8696
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" testvc (options := .quiet)

example : Strata.smtVCsCorrectBoole testvc := by
  gen_smt_vcs_boole
  all_goals (try grind)
