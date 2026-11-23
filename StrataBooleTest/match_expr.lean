/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/--
  lowers to `r:= if(isSome(o)) then get(o) * get(o) else 0;`
-/

/-
# pattern matching expression
Each pattern option lowers to datatype testers as if condition and variables instantiated in if body.
Pattern options nested into if then else statements. Top constructor level checked for exhaustiveness.

TODO:
  - nested-pattern exhaustiveness check
-/

private def pat_match_expr :=
#strata
program Boole;
procedure match_expr_sugar (o : option int) returns(r : int)
spec{
  ensures r >= 0;
}
{
  r := match o {
    some(a : int) => a * a,
    none => 0
  };
};


datatype Triple (a : Type, b : Type, c : Type) {
  MkTriple(fst : a, snd : b, thd : c)
};

procedure match_expr_exhaustiveness (t : Triple int int (option int)) returns(r : int)
spec{
  ensures r >= 0;
}
{
  r := match t {
    MkTriple(a : int, _, _) => a * a
  };
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

Obligation: set_r_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: set_r_calls_option..val_1
Property: assert
Result: ✅ pass

Obligation: match_expr_sugar_ensures_0_611
Property: assert
Result: ✅ pass

Obligation: match_expr_exhaustiveness_ensures_1_886
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" pat_match_expr (options := .quiet)
