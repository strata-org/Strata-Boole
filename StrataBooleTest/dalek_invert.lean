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

Relation to CryptoProver (arXiv 2608.00965):
  CryptoProver verified the scalar module (including `invert`) via Verus+Z3.
  An early AI campaign fabricated an axiom about the internal 27-step squaring
  chain (Fermat exponentiation inside `UnpackedScalar::invert`), which the
  AXIOM-DRIFT gate caught and was later reproved inline.  This benchmark
  independently re-checks the same top-level contract through cvc5 (Level 2)
  and the Lean kernel (Level 3), taking the squaring chain's postcondition as
  a trusted axiom already verified by Verus+Z3.

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

/-
Level 2 — Boole encoding

Each sub-function from the Rust body is declared as an uninterpreted function (UF).
Its Verus-verified postcondition becomes an axiom — the trusted fact cvc5 uses
when chaining through the three-step composition.

Sub-function Verus postconditions (from dalek-lite scalar.rs), encoded as axioms:

  fn unpack(&self) -> (result: UnpackedScalar)           -- Scalar_unpack
    ensures scalar52_as_nat(&result) == scalar_as_nat(self)

  impl UnpackedScalar { fn invert(&self) -> (result: UnpackedScalar) -- UnpackedScalar_invert
    ensures scalar52_as_nat(self) > 0 ==>
      group_canonical(scalar52_as_nat(&result) * scalar52_as_nat(self)) == 1 }
    -- Verus proves this via lemma_group_order_smaller_than_pow256,
    -- lemma_small_mod, and the 27-step Fermat chain s^(group_order-2) mod group_order.
    -- We take the postcondition as a trusted axiom.

  impl UnpackedScalar { fn pack(&self) -> (result: Scalar)  -- UnpackedScalar_pack
    ensures scalar_as_nat(&result) == scalar52_as_nat(self)
    ensures is_canonical_scalar(&result) }
-/
private def invertSeed : StrataDDM.Program :=
#strata
program Boole;

type Scalar;
type UnpackedScalar;

function scalar_as_nat(s: Scalar) : int;
function scalar52_as_nat(u: UnpackedScalar) : int;
function group_canonical(n: int) : int;
function is_canonical_scalar(s: Scalar) : bool;

function Scalar_unpack(self: Scalar) : UnpackedScalar;
function UnpackedScalar_invert(self: UnpackedScalar) : UnpackedScalar;
function UnpackedScalar_pack(self: UnpackedScalar) : Scalar;

axiom (∀ s: Scalar . scalar52_as_nat(Scalar_unpack(s)) == scalar_as_nat(s));
axiom (∀ u: UnpackedScalar . scalar52_as_nat(u) > 0 ==> group_canonical(scalar52_as_nat(UnpackedScalar_invert(u)) * scalar52_as_nat(u)) == 1);
axiom (∀ u: UnpackedScalar . scalar_as_nat(UnpackedScalar_pack(u)) == scalar52_as_nat(u));
axiom (∀ u: UnpackedScalar . is_canonical_scalar(UnpackedScalar_pack(u)));

procedure scalar_invert(s: Scalar) returns (result: Scalar)
spec {
  requires is_canonical_scalar(s);
  ensures (scalar_as_nat(s) > 0 ==>
    group_canonical(scalar_as_nat(result) * scalar_as_nat(s)) == 1);
  ensures is_canonical_scalar(result);
}
{
  var unpacked: UnpackedScalar;
  unpacked := Scalar_unpack(s);
  var inv_unpacked: UnpackedScalar;
  inv_unpacked := UnpackedScalar_invert(unpacked);
  result := UnpackedScalar_pack(inv_unpacked);
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: scalar_invert_ensures_5_3951
Property: assert
Result: ✅ pass

Obligation: scalar_invert_ensures_6_4056
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" invertSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole invertSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
