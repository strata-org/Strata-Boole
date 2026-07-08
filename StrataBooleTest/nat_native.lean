/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import StrataBoole.Nat

open Strata

/-!
# Native Nat Preamble for Boole

`import StrataBoole.Nat` registers the binary-nat library as a native preamble
for the Boole dialect.  Every subsequent `#strata program Boole;` block
automatically has `pos`, `nat`, `nat.toInt`, `nat.fromInt`, the three bridge
axioms, and all arithmetic operators (`nat.add` / `sub` / `mul` / etc.) in
scope — **no explicit declarations needed**.
-/

/-!
## Procedures that use nat without any explicit declarations

The types `pos`, `nat`, and all the nat functions come from the preamble.
-/
private def native_nat_program : StrataDDM.Program :=
#strata
program Boole;

procedure test_nonneg (n : nat) returns ()
spec { ensures 0 <= nat.toInt(n); }
{ assert 0 <= nat.toInt(n); };

procedure test_add_comm (a : nat, b : nat) returns ()
spec { ensures nat.toInt(nat.add(a, b)) == nat.toInt(nat.add(b, a)); }
{ assert nat.toInt(nat.add(a, b)) == nat.toInt(nat.add(b, a)); };

procedure test_fromInt_roundtrip (x : int) returns ()
spec {
  requires 0 <= x;
  ensures nat.toInt(nat.fromInt(x)) == x;
}
{ assert nat.toInt(nat.fromInt(x)) == x; };

procedure test_literal () returns ()
spec { ensures nat.toInt(nat.fromInt(5)) == 5; }
{ assert nat.toInt(nat.fromInt(5)) == 5; };

procedure test_large_literal () returns ()
spec { ensures nat.toInt(nat.fromInt(1024)) == 1024; }
{ assert nat.toInt(nat.fromInt(1024)) == 1024; };

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

Obligation: assert_1_847
Property: assert
Result: ✅ pass

Obligation: test_nonneg_ensures_0_816
Property: assert
Result: ✅ pass

Obligation: assert_3_1004
Property: assert
Result: ✅ pass

Obligation: test_add_comm_ensures_2_938
Property: assert
Result: ✅ pass

Obligation: assert_6_1195
Property: assert
Result: ✅ pass

Obligation: test_fromInt_roundtrip_ensures_5_1151
Property: assert
Result: ✅ pass

Obligation: assert_8_1326
Property: assert
Result: ✅ pass

Obligation: test_literal_ensures_7_1282
Property: assert
Result: ✅ pass

Obligation: assert_10_1469
Property: assert
Result: ✅ pass

Obligation: test_large_literal_ensures_9_1419
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" native_nat_program (options := .quiet)

/-!
## `natLibrary` as a standalone verifiable program

`Strata.BooleNat.natLibrary` is the packaged binary-nat program.  It can be
verified directly, or stitched onto a programmatically-constructed
`StrataDDM.Program` via `Strata.BooleNat.prepend`.
-/
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
Result: ✅ pass-/
#guard_msgs in
open Strata.BooleNat in
#eval Strata.Boole.verify "cvc5" natLibrary (options := .quiet)
