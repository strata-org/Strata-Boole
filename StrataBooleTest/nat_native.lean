/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# Grammar-Level Nat

`nat` and `pos` are declared in the Boole dialect grammar (`StrataBoole.Grammar`).
Every `#strata program Boole;` block has `nat`, `pos`, and the full operator surface
(`nat_toInt`, `nat_fromInt`, `nat_add` / `nat_sub` / `nat_mul` / etc.) in scope
without any explicit declarations.

The binary-nat library (algebraic `pos`/`nat` datatypes with recursive `pos.toInt`)
is automatically injected into the SMT query by `Strata.Boole.verify` when the
compiled program references `nat` or `pos` types.
-/

private def native_nat_program : StrataDDM.Program :=
#strata
program Boole;

procedure test_nonneg (n : nat) returns ()
spec { ensures 0 <= nat_toInt(n); }
{ assert 0 <= nat_toInt(n); };

procedure test_add_comm (a : nat, b : nat) returns ()
spec { ensures nat_toInt(nat_add(a, b)) == nat_toInt(nat_add(b, a)); }
{ assert nat_toInt(nat_add(a, b)) == nat_toInt(nat_add(b, a)); };

procedure test_fromInt_roundtrip (x : int) returns ()
spec {
  requires 0 <= x;
  ensures nat_toInt(nat_fromInt(x)) == x;
}
{ assert nat_toInt(nat_fromInt(x)) == x; };

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

Obligation: assert_1_816
Property: assert
Result: ✅ pass

Obligation: test_nonneg_ensures_0_785
Property: assert
Result: ✅ pass

Obligation: assert_3_973
Property: assert
Result: ✅ pass

Obligation: test_add_comm_ensures_2_907
Property: assert
Result: ✅ pass

Obligation: assert_6_1164
Property: assert
Result: ✅ pass

Obligation: test_fromInt_roundtrip_ensures_5_1120
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" native_nat_program (options := .quiet)

/-!
## Axiom-coverage battery

Tests that natLibrary axioms (round-trip 2, add, sub, literal, monotonicity,
injectivity) are individually provable.  Each is a fast UNSAT query.
-/

private def nat_axiom_battery : StrataDDM.Program :=
#strata
program Boole;

procedure test_roundtrip2 (n : nat) returns ()
spec { ensures nat_fromInt(nat_toInt(n)) == n; }
{ assert nat_fromInt(nat_toInt(n)) == n; };

procedure test_add_correct (a : nat, b : nat) returns ()
spec { ensures nat_toInt(nat_add(a, b)) == nat_toInt(a) + nat_toInt(b); }
{ assert nat_toInt(nat_add(a, b)) == nat_toInt(a) + nat_toInt(b); };

procedure test_sub_correct (a : nat, b : nat) returns ()
spec {
  requires nat_toInt(b) <= nat_toInt(a);
  ensures nat_toInt(nat_sub(a, b)) == nat_toInt(a) - nat_toInt(b);
}
{ assert nat_toInt(nat_sub(a, b)) == nat_toInt(a) - nat_toInt(b); };

procedure test_literal (dummy : int) returns ()
spec { ensures nat_toInt(nat_fromInt(123456)) == 123456; }
{ assert nat_toInt(nat_fromInt(123456)) == 123456; };

procedure test_monotonicity (a : nat, b : nat, c : nat) returns ()
spec {
  requires nat_toInt(a) <= nat_toInt(b);
  ensures nat_toInt(nat_add(a, c)) <= nat_toInt(nat_add(b, c));
}
{ assert nat_toInt(nat_add(a, c)) <= nat_toInt(nat_add(b, c)); };

procedure test_injectivity (a : nat, b : nat) returns ()
spec {
  requires nat_toInt(a) == nat_toInt(b);
  ensures a == b;
}
{ assert a == b; };

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

Obligation: assert_1_2749
Property: assert
Result: ✅ pass

Obligation: test_roundtrip2_ensures_0_2705
Property: assert
Result: ✅ pass

Obligation: assert_3_2925
Property: assert
Result: ✅ pass

Obligation: test_add_correct_ensures_2_2856
Property: assert
Result: ✅ pass

Obligation: test_sub_correct_post_test_sub_correct_ensures_5_3100_calls_nat.sub_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_6_3169_calls_nat.sub_0
Property: assert
Result: ✅ pass

Obligation: assert_6_3169
Property: assert
Result: ✅ pass

Obligation: test_sub_correct_ensures_5_3100
Property: assert
Result: ✅ pass

Obligation: assert_8_3346
Property: assert
Result: ✅ pass

Obligation: test_literal_ensures_7_3292
Property: assert
Result: ✅ pass

Obligation: assert_11_3582
Property: assert
Result: ✅ pass

Obligation: test_monotonicity_ensures_10_3516
Property: assert
Result: ✅ pass

Obligation: assert_14_3774
Property: assert
Result: ✅ pass

Obligation: test_injectivity_ensures_13_3754
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_axiom_battery (options := .quiet)
