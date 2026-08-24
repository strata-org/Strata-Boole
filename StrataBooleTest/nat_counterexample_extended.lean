/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# Extended Nat Counterexample Battery

Additional counterexample and regression tests:
- Range constraint: `2 ≤ nat_toInt(a)` → ensures `nat_toInt(a) == 0` is false
- Integer-list datatype: false head-is-zero claim with a positive requires
- Nonlinear: `nat_toInt(nat_mul(a, a)) < 0` is always false
- User-defined `NatList` with `nat`-typed constructor fields verifies correctly
-/

-- ── Test 3: requires-constrained nat — false claim about a positive nat ───
-- `nat_toInt(a) >= 2` is the requires; the ensures `nat_toInt(a) == 0`
-- is false because any a satisfying the requires has toInt ≥ 2 ≠ 0.
-- With the current solver encoding, cvc5 returns `unknown` (no candidate model).

private def nat_range_prog : StrataDDM.Program :=
#strata
program Boole;

procedure test_nat_range (a : nat) returns ()
spec {
  requires 2 <= nat_toInt(a);
  ensures nat_toInt(a) == 0;
}
{ assert nat_toInt(a) == 0; };

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

Obligation: assert_2_1031
Property: assert
Result: ❓ unknown

Obligation: test_nat_range_ensures_1_1000
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_range_prog (options := .quiet)

-- ── Test 4: user-defined integer-list datatype ─────────────────────────────
-- Declares an `IntList` algebraic datatype with an `int` head field.
-- (Nat-typed datatype fields require a separate preamble extension;
--  this test uses `int` to demonstrate the counterexample workflow
--  for user-defined datatypes.)
-- False claim: "the head of any nonempty list with a positive head is 0".

private def int_list_prog : StrataDDM.Program :=
#strata
program Boole;

datatype IntList () {
  Nil(),
  Cons(head: int, tail: IntList)
};

procedure test_intlist_head (l : IntList) returns ()
spec {
  requires IntList..isCons(l);
  requires 0 < IntList..head(l);
  ensures IntList..head(l) == 0;
}
{ assert IntList..head(l) == 0; };

#end

/-- info:
Obligation: test_intlist_head_pre_test_intlist_head_requires_1_2665_calls_IntList..head_0
Property: assert
Result: ✅ pass

Obligation: test_intlist_head_post_test_intlist_head_ensures_2_2698_calls_IntList..head_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_3_2733_calls_IntList..head_0
Property: assert
Result: ✅ pass

Obligation: assert_3_2733
Property: assert
Result: ❌ fail

Obligation: test_intlist_head_ensures_2_2698
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" int_list_prog (options := .quiet)

-- ── Test 5: nonlinear — square cannot be negative ──────────────────────────
-- `nat_toInt(nat_mul(a, a)) < 0` is always false: any nat² ≥ 0.
-- With the current solver encoding, cvc5 returns `unknown` (no candidate model).

private def nat_square_prog : StrataDDM.Program :=
#strata
program Boole;

procedure test_nat_square (a : nat) returns ()
spec {
  ensures nat_toInt(nat_mul(a, a)) < 0;
}
{ assert nat_toInt(nat_mul(a, a)) < 0; };

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

Obligation: assert_1_3810
Property: assert
Result: ❓ unknown

Obligation: test_nat_square_ensures_0_3768
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_square_prog (options := .quiet)

-- ── Test 6: user-defined NatList datatype with nat-typed constructor fields ──
-- Declares a `NatList` algebraic datatype whose `Cons` constructor carries a
-- `nat`-typed head field.  `coreProgUsesNatOrPos` now scans datatype constructor
-- field types as well as function/procedure headers, so the natLibrary is
-- injected automatically and the `nat` sort is in scope when the type-checker
-- validates the NatList declaration.
-- The property `nat_toInt(head(l)) ≥ 0` is provable (nonneg axiom) and passes.

private def nat_list_prog : StrataDDM.Program :=
#strata
program Boole;

datatype NatList () {
  Nil(),
  Cons(head: nat, tail: NatList)
};

procedure test_natlist_nonneg (l : NatList) returns ()
spec {
  requires NatList..isCons(l);
  ensures nat_toInt(NatList..head(l)) >= 0;
}
{ assert nat_toInt(NatList..head(l)) >= 0; };

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

Obligation: test_natlist_nonneg_post_test_natlist_nonneg_ensures_1_5526_calls_NatList..head_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_2_5572_calls_NatList..head_0
Property: assert
Result: ✅ pass

Obligation: assert_2_5572
Property: assert
Result: ✅ pass

Obligation: test_natlist_nonneg_ensures_1_5526
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_list_prog (options := .quiet)
