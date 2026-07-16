/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# Nat-Injection Detection Path Regression Tests

Verifies that `coreProgUsesNatOrPos` correctly detects nat usage in code paths
fixed by the commits on `nat-binary-datatype`:

* `.ite (.det c)` fix: nat ops appearing **only** in an ite condition expression
  (not in header types, spec, or assert bodies) trigger natLibrary injection.

* `.loop _ _ invs body` fix: nat ops appearing **only** in a loop invariant
  expression trigger natLibrary injection.

* `.quant _ _ _ _ tr b` fix in `lExprUsesNatOrPos`: nat ops in the body of a
  quantifier appearing in a spec `ensures` clause trigger natLibrary injection.

Each test procedure has `int`-only header types and no nat in assert bodies so
that, if a fix is reverted, the detection code returns false, natLibrary is not
injected, the `nat` sort is undefined in the SMT encoding, and the test fails —
providing regression coverage for every detection path.
-/

-- ── Test A: nat ops only in an ite condition ─────────────────────────────────
-- The condition `nat_lt(nat_fromInt(0), nat_fromInt(1))` references nat ops.
-- Both branches assign a non-negative constant so the ensures `r >= 0` is
-- trivially provable once natLibrary is injected and the ite is encoded in SMT.

private def ite_cond_prog : StrataDDM.Program :=
#strata
program Boole;

procedure test_ite_cond (x : int) returns (r : int)
spec { ensures r >= 0; }
{
  if (nat_lt(nat_fromInt(0), nat_fromInt(1))) {
    r := 1;
  } else {
    r := 0;
  }
};

#end

/-- info:
Obligation: pos.toInt_body_calls_pos..xO_h_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_body_calls_pos..xI_h_1
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: nat.toInt_body_calls_nat..val_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_2
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_3
Property: assert
Result: ✅ pass

Obligation: test_ite_cond_ensures_0_1568
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" ite_cond_prog (options := .quiet)

-- ── Test B: nat ops only in a while-loop invariant ───────────────────────────
-- The invariant `nat_toInt(nat_fromInt(0)) == 0` is a ground tautology that
-- forces natLibrary injection via the `.loop _ _ invs body` scan.

private def loop_inv_prog : StrataDDM.Program :=
#strata
program Boole;

procedure test_loop_inv (n : int) returns ()
spec { requires 0 <= n; }
{
  var i : int := 0;
  while(i < n)
    invariant nat_toInt(nat_fromInt(0)) == 0
  {
    i := i + 1;
  }
};

#end

/-- info:
Obligation: pos.toInt_body_calls_pos..xO_h_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_body_calls_pos..xI_h_1
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: nat.toInt_body_calls_nat..val_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_2
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_3
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" loop_inv_prog (options := .quiet)

-- ── Test C: nat ops only in a spec-ensures quantifier body ───────────────────
-- The ensures `∀ n:nat . 0 <= nat_toInt(n)` has `int`-typed header, no nat
-- in the body assert, and no nat-typed locals.  Detection succeeds only if
-- `lExprUsesNatOrPos` recurses into the quantifier body (the `.quant` case fix).
-- The claim itself is the nat_nonneg axiom and is UNSAT for its negation.

private def spec_quant_prog : StrataDDM.Program :=
#strata
program Boole;

procedure test_spec_quant (dummy : int) returns ()
spec {
  ensures ∀ n:nat . 0 <= nat_toInt(n);
}
{
  assert 0 <= dummy || 0 > dummy;
};

#end

/-- info:
Obligation: pos.toInt_body_calls_pos..xO_h_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_body_calls_pos..xI_h_1
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: nat.toInt_body_calls_nat..val_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_2
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_3
Property: assert
Result: ✅ pass

Obligation: assert_1_4595
Property: assert
Result: ✅ pass

Obligation: test_spec_quant_ensures_0_4549
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" spec_quant_prog (options := .quiet)
