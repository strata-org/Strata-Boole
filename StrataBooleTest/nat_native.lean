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
