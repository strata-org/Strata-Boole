/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchor:
- Source: dalek-lite `curve25519-dalek/src/scalar.rs`
  (`from_bytes_mod_order_wide`, B2) and `from_bytes_mod_order` (B2/B5).
  Rust `u8 as usize`, `u64 as u128`, etc. are widening casts; this seed
  exercises the Boole `as_uint(e)` surface syntax for all supported widths
  (bv W1, bv W8, bv W16, bv W32, bv W64, bv W128).

Feature: `as_uint(e)` — widening cast from any bitvector type to `int`.

Lowers to a native `Bv{n}.ToUInt : bvN → int` Core op; the SMT encoder maps
it to the SMT-LIB 2.7 `ubv_to_int` function. No axioms injected.
-/

private def castExprSeed : StrataDDM.Program :=
#strata
program Boole;

procedure cast_bv8_nonneg(x: bv W8) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv64_nonneg(x: bv W64) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv32_bounded(x: bv W32) returns ()
spec {
  ensures 0 <= as_uint(x) && as_uint(x) < 4294967296;
}
{
  assert 0 <= as_uint(x) && as_uint(x) < 4294967296;
};

procedure cast_bv1_nonneg(x: bv W1) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv16_nonneg(x: bv W16) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv128_nonneg(x: bv W128) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};
#end

/-- info:
Obligation: assert_1_862
Property: assert
Result: ✅ pass

Obligation: cast_bv8_nonneg_ensures_0_831
Property: assert
Result: ✅ pass

Obligation: assert_3_979
Property: assert
Result: ✅ pass

Obligation: cast_bv64_nonneg_ensures_2_948
Property: assert
Result: ✅ pass

Obligation: assert_5_1124
Property: assert
Result: ✅ pass

Obligation: cast_bv32_bounded_ensures_4_1066
Property: assert
Result: ✅ pass

Obligation: assert_7_1266
Property: assert
Result: ✅ pass

Obligation: cast_bv1_nonneg_ensures_6_1235
Property: assert
Result: ✅ pass

Obligation: assert_9_1383
Property: assert
Result: ✅ pass

Obligation: cast_bv16_nonneg_ensures_8_1352
Property: assert
Result: ✅ pass

Obligation: assert_11_1502
Property: assert
Result: ✅ pass

Obligation: cast_bv128_nonneg_ensures_10_1471
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" castExprSeed (options := .quiet)
