/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: scalar invert — multiplicative inverse mod ℓ
Source: dalek-lite `curve25519-dalek/src/scalar.rs`

Security relevance:
  - For nonzero s, s⁻¹ × s ≡ 1 (mod ℓ).
    A wrong invert silently corrupts Ed25519 signing and Ristretto batch ops.
  - Result must remain in canonical range [0, ℓ).

Level 1 — Verus source (verbatim):

  // VERIFICATION NOTE: VERIFIED
  pub fn invert(&self) -> (result: Scalar)
      requires
          is_canonical_scalar(self),
      ensures
          scalar_as_nat(self) > 0 ==> group_canonical(
              scalar_as_nat(&result) * scalar_as_nat(self),
          ) == 1,
          is_canonical_scalar(&result),
  {
      let unpacked = self.unpack();
      let inv_unpacked = unpacked.invert();
      let result = inv_unpacked.pack();
      proof {
          lemma_group_order_smaller_than_pow256();
          lemma_small_mod(scalar52_as_nat(&inv_unpacked), pow2(256));
          if scalar_as_nat(self) > 0 {
              lemma_small_mod(scalar52_as_nat(&unpacked), group_order());
              assert((u8_32_as_nat(&result.bytes) * u8_32_as_nat(&self.bytes))
                  % group_order() == 1);
          }
      }
      result
  }
-/

-- Level 2 — Boole encoding
-- The implementation chains three calls: unpack_fn → invert_unpacked_fn → pack_fn.
-- Axioms capture each function's postcondition so cvc5 must chain equalities
-- through two intermediate types (Scalar → UnpackedScalar → Scalar) rather
-- than looking up a single axiom about the top-level operation.
private def invertSeed : StrataDDM.Program :=
#strata
program Boole;

type Scalar;
type UnpackedScalar;

function unpack_fn(s: Scalar) : UnpackedScalar;
function invert_unpacked_fn(u: UnpackedScalar) : UnpackedScalar;
function pack_fn(u: UnpackedScalar) : Scalar;

function scalar_as_nat(s: Scalar) : int;
function unpacked_as_nat(u: UnpackedScalar) : int;
function group_canonical(n: int) : int;
function is_canonical_scalar(s: Scalar) : bool;

axiom (∀ s: Scalar . unpacked_as_nat(unpack_fn(s)) == scalar_as_nat(s));
axiom (∀ u: UnpackedScalar . unpacked_as_nat(u) > 0 ==> group_canonical(unpacked_as_nat(invert_unpacked_fn(u)) * unpacked_as_nat(u)) == 1);
axiom (∀ u: UnpackedScalar . scalar_as_nat(pack_fn(u)) == unpacked_as_nat(u));
axiom (∀ u: UnpackedScalar . is_canonical_scalar(pack_fn(u)));

procedure scalar_invert(s: Scalar) returns (result: Scalar)
spec {
  requires is_canonical_scalar(s);
  ensures (scalar_as_nat(s) > 0 ==>
    group_canonical(scalar_as_nat(result) * scalar_as_nat(s)) == 1);
  ensures is_canonical_scalar(result);
}
{
  var unpacked: UnpackedScalar;
  unpacked := unpack_fn(s);
  var inv_unpacked: UnpackedScalar;
  inv_unpacked := invert_unpacked_fn(unpacked);
  result := pack_fn(inv_unpacked);
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: scalar_invert_ensures_5_2601
Property: assert
Result: ✅ pass

Obligation: scalar_invert_ensures_6_2706
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" invertSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole invertSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
