/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: montgomery_invert — the 27-step scalar inversion addition chain
Source: dalek-lite `curve25519-dalek/src/scalar.rs`, `impl UnpackedScalar`
        (chain from https://briansmith.org/ecc-inversion-addition-chains-01)

What is proved:
  The chain of 248 Montgomery squarings and 36 multiplications computes
  s^(ℓ-2), where ℓ = 2^252 + 27742317777372353535851937790883648493 is the
  Ed25519 group order.  ℓ is prime, so by Fermat s^(ℓ-2) · s = s^(ℓ-1) = 1:
  the result is s⁻¹ (mod ℓ).  Change any one of the 27 squaring counts or
  operands and the final exponent is no longer ℓ-2 — the proof fails.

Relation to CryptoProver (arXiv 2608.00965):
  This is the function about which an early AI campaign fabricated an axiom
  ("27-step scalar inversion chain") that the AXIOM-DRIFT gate rejected.  It
  was then proved inline in Verus with a ghost exponent `e_y` updated after
  each square_multiply and closed by `lemma_chain_exp_is_l_minus_2`.  This
  benchmark re-checks the same exponent bookkeeping through cvc5 (Level 2)
  and the Lean kernel (Level 3).

Level 1 — Verus source (verbatim; proof blocks and ghost bookkeeping elided):

  pub fn montgomery_invert(&self) -> (result: UnpackedScalar)
      requires
          is_canonical_scalar52(self),
      ensures
          limb_prod_bounded_u128(result.limbs, result.limbs, 5),
          is_canonical_scalar52(&result),
          // result * self ≡ R² (mod L), i.e. from_montgomery(result) * from_montgomery(self) ≡ 1 (mod L)
          scalar52_as_nat(self) > 0 ==> group_canonical(
              scalar52_as_nat(&result) * scalar52_as_nat(self),
          ) == group_canonical(montgomery_radix() * montgomery_radix()),
  {
      let    _1 = *self;
      let   _10 = _1.montgomery_square();
      let  _100 = _10.montgomery_square();
      let   _11 = UnpackedScalar::montgomery_mul(&_10,     &_1);
      let  _101 = UnpackedScalar::montgomery_mul(&_10,    &_11);
      let  _111 = UnpackedScalar::montgomery_mul(&_10,   &_101);
      let _1001 = UnpackedScalar::montgomery_mul(&_10,   &_111);
      let _1011 = UnpackedScalar::montgomery_mul(&_10,  &_1001);
      let _1111 = UnpackedScalar::montgomery_mul(&_100, &_1011);

      let mut y = UnpackedScalar::montgomery_mul(&_1111, &_1);

      fn square_multiply(y: &mut UnpackedScalar, squarings: usize, x: &UnpackedScalar) {
          for _ in 0..squarings {
              *y = y.montgomery_square();
          }
          *y = UnpackedScalar::montgomery_mul(y, x);
      }

      square_multiply(&mut y, 123 + 3, &_101);
      square_multiply(&mut y,   2 + 2, &_11);
      square_multiply(&mut y,   1 + 4, &_1111);
      square_multiply(&mut y,   1 + 4, &_1111);
      square_multiply(&mut y,       4, &_1001);
      square_multiply(&mut y,       2, &_11);
      square_multiply(&mut y,   1 + 4, &_1111);
      square_multiply(&mut y,   1 + 3, &_101);
      square_multiply(&mut y,   3 + 3, &_101);
      square_multiply(&mut y,       3, &_111);
      square_multiply(&mut y,   1 + 4, &_1111);
      square_multiply(&mut y,   2 + 3, &_111);
      square_multiply(&mut y,   2 + 2, &_11);
      square_multiply(&mut y,   1 + 4, &_1011);
      square_multiply(&mut y,   2 + 4, &_1011);
      square_multiply(&mut y,   6 + 4, &_1001);
      square_multiply(&mut y,   2 + 2, &_11);
      square_multiply(&mut y,   3 + 2, &_11);
      square_multiply(&mut y,   3 + 2, &_11);
      square_multiply(&mut y,   1 + 4, &_1001);
      square_multiply(&mut y,   1 + 3, &_111);
      square_multiply(&mut y,   2 + 4, &_1111);
      square_multiply(&mut y,   1 + 4, &_1011);
      square_multiply(&mut y,       3, &_101);
      square_multiply(&mut y,   2 + 4, &_1111);
      square_multiply(&mut y,       3, &_101);
      square_multiply(&mut y,   1 + 2, &_11);

      y
  }
-/

/-
Level 2 — Boole encoding

  pow(s, e)  : Montgomery-form representative of s^e (uninterpreted).
  montgomery_square / montgomery_mul : procedure stubs.  Their contracts are the
    exponent laws dalek-lite proves for them (lemma_square_multiply_step,
    lemma_montgomery_mul_exponent_add): squaring doubles the exponent,
    multiplying adds exponents.  Each takes the ghost base `s` and exponent(s)
    as extra parameters, as the Verus lemmas do.
  square_K / square_multiply_K : the `for _ in 0..squarings` loop unrolled for
    each squaring count K the chain uses (2, 3, 4, 5, 6, 10, 126).
  e : ghost exponent, mirrors Verus' `e_y`.  The top-level obligation is that
    after 27 steps it equals group_order() - 2 — 253-bit arithmetic that cvc5
    discharges directly.

  Not re-encoded: the Fermat step s^(ℓ-1) = 1 (dalek-lite takes ℓ prime as
  `axiom_group_order_is_prime`), and the limb-level Montgomery arithmetic
  inside montgomery_square / montgomery_mul (verified separately by Verus).
-/
private def montgomeryInvertSeed : StrataDDM.Program :=
#strata
program Boole;

type UnpackedScalar;

function pow(base: UnpackedScalar, e: int) : UnpackedScalar;
function group_order() : int;

axiom group_order() == 7237005577332262213973186563042994240857116359379907606001950938285454250989;
axiom (∀ s: UnpackedScalar . pow(s, 1) == s);

procedure montgomery_square(s: UnpackedScalar, y: UnpackedScalar, e: int) returns (r: UnpackedScalar)
spec {
  requires y == pow(s, e);
  ensures r == pow(s, 2 * e);
}
{ assume false; };

procedure montgomery_mul(s: UnpackedScalar, a: UnpackedScalar, ea: int, b: UnpackedScalar, eb: int) returns (r: UnpackedScalar)
spec {
  requires a == pow(s, ea);
  requires b == pow(s, eb);
  ensures r == pow(s, ea + eb);
}
{ assume false; };

procedure square_2(s: UnpackedScalar, y: UnpackedScalar, e: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  ensures e2 == 4 * e;
  ensures r == pow(s, e2);
}
{
  r := y;
  e2 := e;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
};

procedure square_3(s: UnpackedScalar, y: UnpackedScalar, e: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  ensures e2 == 8 * e;
  ensures r == pow(s, e2);
}
{
  r := y;
  e2 := e;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
};

procedure square_4(s: UnpackedScalar, y: UnpackedScalar, e: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  ensures e2 == 16 * e;
  ensures r == pow(s, e2);
}
{
  r := y;
  e2 := e;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
};

procedure square_5(s: UnpackedScalar, y: UnpackedScalar, e: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  ensures e2 == 32 * e;
  ensures r == pow(s, e2);
}
{
  r := y;
  e2 := e;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
};

procedure square_6(s: UnpackedScalar, y: UnpackedScalar, e: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  ensures e2 == 64 * e;
  ensures r == pow(s, e2);
}
{
  r := y;
  e2 := e;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
};

procedure square_10(s: UnpackedScalar, y: UnpackedScalar, e: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  ensures e2 == 1024 * e;
  ensures r == pow(s, e2);
}
{
  r := y;
  e2 := e;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
  call r := montgomery_square(s, r, e2);
  e2 := 2 * e2;
};

procedure square_126(s: UnpackedScalar, y: UnpackedScalar, e: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  ensures e2 == 85070591730234615865843651857942052864 * e;
  ensures r == pow(s, e2);
}
{
  r := y;
  e2 := e;
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_10(s, r, e2);
  call r, e2 := square_6(s, r, e2);
};

procedure square_multiply_2(s: UnpackedScalar, y: UnpackedScalar, e: int, x: UnpackedScalar, f: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  requires x == pow(s, f);
  ensures e2 == 4 * e + f;
  ensures r == pow(s, e2);
}
{
  call r, e2 := square_2(s, y, e);
  call r := montgomery_mul(s, r, e2, x, f);
  e2 := e2 + f;
};

procedure square_multiply_3(s: UnpackedScalar, y: UnpackedScalar, e: int, x: UnpackedScalar, f: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  requires x == pow(s, f);
  ensures e2 == 8 * e + f;
  ensures r == pow(s, e2);
}
{
  call r, e2 := square_3(s, y, e);
  call r := montgomery_mul(s, r, e2, x, f);
  e2 := e2 + f;
};

procedure square_multiply_4(s: UnpackedScalar, y: UnpackedScalar, e: int, x: UnpackedScalar, f: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  requires x == pow(s, f);
  ensures e2 == 16 * e + f;
  ensures r == pow(s, e2);
}
{
  call r, e2 := square_4(s, y, e);
  call r := montgomery_mul(s, r, e2, x, f);
  e2 := e2 + f;
};

procedure square_multiply_5(s: UnpackedScalar, y: UnpackedScalar, e: int, x: UnpackedScalar, f: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  requires x == pow(s, f);
  ensures e2 == 32 * e + f;
  ensures r == pow(s, e2);
}
{
  call r, e2 := square_5(s, y, e);
  call r := montgomery_mul(s, r, e2, x, f);
  e2 := e2 + f;
};

procedure square_multiply_6(s: UnpackedScalar, y: UnpackedScalar, e: int, x: UnpackedScalar, f: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  requires x == pow(s, f);
  ensures e2 == 64 * e + f;
  ensures r == pow(s, e2);
}
{
  call r, e2 := square_6(s, y, e);
  call r := montgomery_mul(s, r, e2, x, f);
  e2 := e2 + f;
};

procedure square_multiply_10(s: UnpackedScalar, y: UnpackedScalar, e: int, x: UnpackedScalar, f: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  requires x == pow(s, f);
  ensures e2 == 1024 * e + f;
  ensures r == pow(s, e2);
}
{
  call r, e2 := square_10(s, y, e);
  call r := montgomery_mul(s, r, e2, x, f);
  e2 := e2 + f;
};

procedure square_multiply_126(s: UnpackedScalar, y: UnpackedScalar, e: int, x: UnpackedScalar, f: int) returns (r: UnpackedScalar, e2: int)
spec {
  requires y == pow(s, e);
  requires x == pow(s, f);
  ensures e2 == 85070591730234615865843651857942052864 * e + f;
  ensures r == pow(s, e2);
}
{
  call r, e2 := square_126(s, y, e);
  call r := montgomery_mul(s, r, e2, x, f);
  e2 := e2 + f;
};

procedure montgomery_invert(s: UnpackedScalar) returns (result: UnpackedScalar)
spec {
  ensures result == pow(s, group_order() - 2);
}
{
  var _1: UnpackedScalar;
  var _10: UnpackedScalar;
  var _100: UnpackedScalar;
  var _11: UnpackedScalar;
  var _101: UnpackedScalar;
  var _111: UnpackedScalar;
  var _1001: UnpackedScalar;
  var _1011: UnpackedScalar;
  var _1111: UnpackedScalar;
  var y: UnpackedScalar;
  var e: int;
  _1 := s;
  call _10 := montgomery_square(s, _1, 1);
  call _100 := montgomery_square(s, _10, 2);
  call _11 := montgomery_mul(s, _10, 2, _1, 1);
  call _101 := montgomery_mul(s, _10, 2, _11, 3);
  call _111 := montgomery_mul(s, _10, 2, _101, 5);
  call _1001 := montgomery_mul(s, _10, 2, _111, 7);
  call _1011 := montgomery_mul(s, _10, 2, _1001, 9);
  call _1111 := montgomery_mul(s, _100, 4, _1011, 11);
  call y := montgomery_mul(s, _1111, 15, _1, 1);
  e := 16;
  call y, e := square_multiply_126(s, y, e, _101, 5);
  call y, e := square_multiply_4(s, y, e, _11, 3);
  call y, e := square_multiply_5(s, y, e, _1111, 15);
  call y, e := square_multiply_5(s, y, e, _1111, 15);
  call y, e := square_multiply_4(s, y, e, _1001, 9);
  call y, e := square_multiply_2(s, y, e, _11, 3);
  call y, e := square_multiply_5(s, y, e, _1111, 15);
  call y, e := square_multiply_4(s, y, e, _101, 5);
  call y, e := square_multiply_6(s, y, e, _101, 5);
  call y, e := square_multiply_3(s, y, e, _111, 7);
  call y, e := square_multiply_5(s, y, e, _1111, 15);
  call y, e := square_multiply_5(s, y, e, _111, 7);
  call y, e := square_multiply_4(s, y, e, _11, 3);
  call y, e := square_multiply_5(s, y, e, _1011, 11);
  call y, e := square_multiply_6(s, y, e, _1011, 11);
  call y, e := square_multiply_10(s, y, e, _1001, 9);
  call y, e := square_multiply_4(s, y, e, _11, 3);
  call y, e := square_multiply_5(s, y, e, _11, 3);
  call y, e := square_multiply_5(s, y, e, _11, 3);
  call y, e := square_multiply_5(s, y, e, _1001, 9);
  call y, e := square_multiply_4(s, y, e, _111, 7);
  call y, e := square_multiply_6(s, y, e, _1111, 15);
  call y, e := square_multiply_5(s, y, e, _1011, 11);
  call y, e := square_multiply_3(s, y, e, _101, 5);
  call y, e := square_multiply_6(s, y, e, _1111, 15);
  call y, e := square_multiply_3(s, y, e, _101, 5);
  call y, e := square_multiply_3(s, y, e, _11, 3);
  result := y;
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: montgomery_square_ensures_3_5458
Property: assert
Result: ✅ pass

Obligation: montgomery_mul_ensures_7_5701
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_4
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_10
Property: assert
Result: ✅ pass

Obligation: square_2_ensures_10_5891
Property: assert
Result: ✅ pass

Obligation: square_2_ensures_11_5914
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_16
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_22
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_28
Property: assert
Result: ✅ pass

Obligation: square_3_ensures_13_6220
Property: assert
Result: ✅ pass

Obligation: square_3_ensures_14_6243
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_34
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_40
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_46
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_52
Property: assert
Result: ✅ pass

Obligation: square_4_ensures_16_6606
Property: assert
Result: ✅ pass

Obligation: square_4_ensures_17_6630
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_58
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_64
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_70
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_76
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_82
Property: assert
Result: ✅ pass

Obligation: square_5_ensures_19_7050
Property: assert
Result: ✅ pass

Obligation: square_5_ensures_20_7074
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_88
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_94
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_100
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_106
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_112
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_118
Property: assert
Result: ✅ pass

Obligation: square_6_ensures_22_7551
Property: assert
Result: ✅ pass

Obligation: square_6_ensures_23_7575
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_124
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_130
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_136
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_142
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_148
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_154
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_160
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_166
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_172
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_178
Property: assert
Result: ✅ pass

Obligation: square_10_ensures_25_8110
Property: assert
Result: ✅ pass

Obligation: square_10_ensures_26_8136
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_185
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_193
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_201
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_209
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_217
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_225
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_233
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_241
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_249
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_257
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_265
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_273
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_6_requires_21_7524_281
Property: assert
Result: ✅ pass

Obligation: square_126_ensures_28_8900
Property: assert
Result: ✅ pass

Obligation: square_126_ensures_29_8960
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_2_requires_9_5864_289
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_298
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_299
Property: assert
Result: ✅ pass

Obligation: square_multiply_2_ensures_32_9695
Property: assert
Result: ✅ pass

Obligation: square_multiply_2_ensures_33_9722
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_3_requires_12_6193_306
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_315
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_316
Property: assert
Result: ✅ pass

Obligation: square_multiply_3_ensures_36_10051
Property: assert
Result: ✅ pass

Obligation: square_multiply_3_ensures_37_10078
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_4_requires_15_6579_323
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_332
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_333
Property: assert
Result: ✅ pass

Obligation: square_multiply_4_ensures_40_10407
Property: assert
Result: ✅ pass

Obligation: square_multiply_4_ensures_41_10435
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_5_requires_18_7023_340
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_349
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_350
Property: assert
Result: ✅ pass

Obligation: square_multiply_5_ensures_44_10764
Property: assert
Result: ✅ pass

Obligation: square_multiply_5_ensures_45_10792
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_6_requires_21_7524_357
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_366
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_367
Property: assert
Result: ✅ pass

Obligation: square_multiply_6_ensures_48_11121
Property: assert
Result: ✅ pass

Obligation: square_multiply_6_ensures_49_11149
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_10_requires_24_8083_374
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_383
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_384
Property: assert
Result: ✅ pass

Obligation: square_multiply_10_ensures_52_11479
Property: assert
Result: ✅ pass

Obligation: square_multiply_10_ensures_53_11509
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_126_requires_27_8873_391
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_400
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_401
Property: assert
Result: ✅ pass

Obligation: square_multiply_126_ensures_56_11841
Property: assert
Result: ✅ pass

Obligation: square_multiply_126_ensures_57_11905
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_407
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_square_requires_2_5431_413
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_421
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_422
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_430
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_431
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_439
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_440
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_448
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_449
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_457
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_458
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_466
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_467
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_5_5645_475
Property: assert
Result: ✅ pass

Obligation: callElimAssert_montgomery_mul_requires_6_5673_476
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_126_requires_54_11787_485
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_126_requires_55_11814_486
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_38_10353_496
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_39_10380_497
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_507
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_508
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_518
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_519
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_38_10353_529
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_39_10380_530
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_2_requires_30_9641_540
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_2_requires_31_9668_541
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_551
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_552
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_38_10353_562
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_39_10380_563
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_6_requires_46_11067_573
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_6_requires_47_11094_574
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_3_requires_34_9997_584
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_3_requires_35_10024_585
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_595
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_596
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_606
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_607
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_38_10353_617
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_39_10380_618
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_628
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_629
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_6_requires_46_11067_639
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_6_requires_47_11094_640
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_10_requires_50_11425_650
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_10_requires_51_11452_651
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_38_10353_661
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_39_10380_662
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_672
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_673
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_683
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_684
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_694
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_695
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_38_10353_705
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_4_requires_39_10380_706
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_6_requires_46_11067_716
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_6_requires_47_11094_717
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_42_10710_727
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_5_requires_43_10737_728
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_3_requires_34_9997_738
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_3_requires_35_10024_739
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_6_requires_46_11067_749
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_6_requires_47_11094_750
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_3_requires_34_9997_760
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_3_requires_35_10024_761
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_3_requires_34_9997_771
Property: assert
Result: ✅ pass

Obligation: callElimAssert_square_multiply_3_requires_35_10024_772
Property: assert
Result: ✅ pass

Obligation: montgomery_invert_ensures_58_12124
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" montgomeryInvertSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole montgomeryInvertSeed := by
  gen_smt_vcs_boole
  all_goals smt
