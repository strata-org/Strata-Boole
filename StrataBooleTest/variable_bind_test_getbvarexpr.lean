/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
Regression test for `getBVarExpr`
`getBVarExpr` previously substituted variables with and without a binder the same way,
but could contain `.bvar`s or substituted expressions (e.g. pattern selectors).

fix: only count actual `.bvar` as binders and lift substituted expressions over newly introduced binders

the pattern variable `x` is substituted by an expression referring to outer binder `i`.
Under `∀ j`, that expression must be lifted so `i` remains in scope.
-/

private def getBVarExpr_regression :=
#strata
program Boole;


procedure pattern_match_quantified (s : Map int (option int))
spec {
  requires ∀ i : int :: (s[i] matches some(v : int) ==> v == i);
}
{
  assert ∀ i : int ::
    (s[i] matches some(x : int) ==> (∀ j : int :: x == i && j == j));
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

Obligation: pattern_match_quantified_pre_pattern_match_quantified_requires_0_740_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_1_811_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_1_811
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" getBVarExpr_regression (options := .quiet)
