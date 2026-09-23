/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# Nat Counterexample Battery

Tests the verifier's response to false nat properties.

The Strata nat/pos commit (`764b03165`) preserves cvc5 candidate models through
`SMT.Result.merge` and promotes them via the candidate-validation phase.
nat-arithmetic counterexample queries now return `❌ fail` with a certified
counterexample instead of `❓ unknown`.  Obligations the primary pass still
leaves `unknown` are re-queried with the computable form of the library
(`pos.toInt`/`pos.fromInt` as `define-fun-rec`, cvc5 `fmf-fun`); see Test 2.
-/

-- ── Test 1: simple false claim ─────────────────────────────────────────────
-- nat_toInt(a) < nat_toInt(b) does not hold in general; cvc5 returns a
-- concrete counterexample.

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

Obligation: assert_1_1134
Property: assert
Result: ❌ fail

Obligation: test_false_lt_ensures_0_1093
Property: assert
Result: ❌ fail-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_false_lt_prog (options := .quiet)

-- ── Test 2: constrained sum — unique counterexample ───────────────────────
-- Given nat_toInt(a) = 73 and nat_toInt(a + b) = 200, it must be that
-- nat_toInt(b) = 127.  The verifier cannot prove nat_toInt(b) = 0.
--
-- The primary pass (nat library as uninterpreted symbols + axioms) returns
-- `unknown` with a candidate that violates the requires (e.g. a = 2, b = 4).
-- `Boole.verify` then re-queries the unknown obligations with the computable
-- library (`pos.toInt`/`pos.fromInt` as `define-fun-rec`, cvc5 `fmf-fun`) and
-- cvc5 finds the unique counterexample b = 127: the result is ❌ fail.

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

Obligation: assert_3_2911
Property: assert
Result: ❌ fail

Obligation: test_sum_counterexample_ensures_2_2880
Property: assert
Result: ❌ fail-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_sum_prog (options := .quiet)

-- Without the re-query the primary pass alone is reported: `unknown`.
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

Obligation: assert_3_2911
Property: assert
Result: ❓ unknown

Obligation: test_sum_counterexample_ensures_2_2880
Property: assert
Result: ❓ unknown-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_sum_prog (options := .quiet) (natRequery := false)

-- The same run with models: the constructor terms are decoded to integers
-- (`Npos(xI(xO(xO(xI(xO(xO(xH)))))))` is 73) before display.
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

Obligation: assert_3_2911
Property: assert
Result: ❌ fail
Model:
(x@1, 0) (b@1, 127) (p@1, 1) (a@1, 73) (p@2, 1) 

Obligation: test_sum_counterexample_ensures_2_2880
Property: assert
Result: ❌ fail
Model:
(x@1, 0) (b@1, 127) (p@1, 1) (a@1, 73) (p@2, 1)-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_sum_prog
  (options := { _root_.Core.VerifyOptions.quiet with verbose := .models })
