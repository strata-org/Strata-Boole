/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# Nat Counterexample Battery

Tests the verifier's response to false nat properties.

With the current Strata version and the programmatic `natCorePreamble` encoding,
cvc5 returns `❓ unknown` for nat-arithmetic counterexample queries: the solver
cannot ground the quantified nat axioms into a concrete model within the time
limit. A future Strata bump (with improved solver encoding) is expected to
promote these to `❌ fail` via the candidate-validation phase.
-/

-- ── Test 1: simple false claim ─────────────────────────────────────────────
-- nat_toInt(a) < nat_toInt(b) does not hold in general.
-- With the current solver encoding, cvc5 returns `unknown` (no candidate model).

private def nat_false_lt_prog : StrataDDM.Program :=
#strata
program Boole;

procedure test_false_lt (a : nat, b : nat) returns ()
spec { ensures nat_toInt(a) < nat_toInt(b); }
{ assert nat_toInt(a) < nat_toInt(b); };

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

Obligation: assert_1_1096
Property: assert
Result: ❓ unknown

Obligation: test_false_lt_ensures_0_1055
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_false_lt_prog (options := .quiet)

-- ── Test 2: constrained sum — unique counterexample ───────────────────────
-- Given nat_toInt(a) = 73 and nat_toInt(a + b) = 200, it must be that
-- nat_toInt(b) = 127.  The verifier cannot prove nat_toInt(b) = 0.
--
-- NOTE: cvc5 returns `unknown` with a partial candidate (e.g. a=2, b=4) that
-- violates the requires.  The candidate validator rejects it, and the re-query
-- also times out.  The result is ❓ unknown — a conservative sound response.
-- (With a longer timeout or a fine-tuned solver config the result becomes ❌ fail.)

private def nat_sum_prog : StrataDDM.Program :=
#strata
program Boole;

procedure test_sum_counterexample (a : nat, b : nat) returns ()
spec {
  requires nat_toInt(a) == 73;
  requires nat_toInt(nat_add(a, b)) == 200;
  ensures nat_toInt(b) == 0;
}
{ assert nat_toInt(b) == 0; };

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

Obligation: assert_3_2900
Property: assert
Result: ❓ unknown

Obligation: test_sum_counterexample_ensures_2_2869
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_sum_prog (options := .quiet)
