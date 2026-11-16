/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
Regression test: the initial value of a `for` loop is read outside the scope of the loop
variable.

The grammar scopes the guard, the step, the invariants and the body of a `for` under its loop
variable, but not the initial value. A variable in the initial value therefore resolves as it
does just before the loop. Each procedure below starts its loop from a parameter and verifies
only if the loop starts there: one `for ... to`, one `for ... downto`, one `for (...; ...; ...)`.
-/

private def forLoopInit : StrataDDM.Program :=
#strata
program Boole;

procedure count_up (lo: int, hi: int) returns (r: int)
spec {
  requires [ordered]: (lo <= hi);
  ensures [counted_up]: (r == hi - lo + 1);
}
{
  r := 0;
  for i : int := lo to hi
    invariant lo <= i && i <= hi + 1
    invariant r == i - lo
  {
    r := r + 1;
  }
};

procedure count_down (n: int) returns (r: int)
spec {
  requires [nonneg]: (n >= 0);
  ensures [counted_down]: (r == n + 1);
}
{
  r := 0;
  for i : int := n downto 0
    invariant -1 <= i && i <= n
    invariant r == n - i
  {
    r := r + 1;
  }
};

procedure count_general (lo: int, hi: int) returns (r: int)
spec {
  requires [ordered]: (lo <= hi);
  ensures [counted_general]: (r == hi - lo + 1);
}
{
  r := 0;
  for (i : int := lo; i <= hi; i + 1)
    invariant lo <= i && i <= hi + 1
    invariant r == i - lo
  {
    r := r + 1;
  }
};
#end

/-- info:
Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: counted_up
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_1_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_1_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_1
Property: assert
Result: ✅ pass

Obligation: counted_down
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_2_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_2_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_2_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_2_1
Property: assert
Result: ✅ pass

Obligation: counted_general
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" forLoopInit (options := .quiet)

theorem forLoopInit_smtVCsCorrect : smtVCsCorrectBoole forLoopInit := by
  gen_smt_vcs_boole
  all_goals grind
