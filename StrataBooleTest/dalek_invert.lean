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
  and the Lean kernel (Level 3), abstracting the squaring chain to a single
  procedure stub whose postcondition was already verified by Verus.

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

Each callee is a procedure stub: `spec { ensures ... }` carries its
Verus-verified postcondition; `assume false` marks the body as opaque.
After each `call`, cvc5 assumes the callee's ensures as a fact.

Sub-function Verus postconditions (from dalek-lite scalar.rs):

  fn unpack(&self) -> (result: Scalar52)
    ensures scalar52_as_nat(&result) == scalar_as_nat(self)

  impl Scalar52 { fn invert(&self) -> (result: Scalar52)
    ensures scalar52_as_nat(self) > 0 ==>
      group_canonical(scalar52_as_nat(&result) * scalar52_as_nat(self)) == 1 }

  impl Scalar52 { fn pack(&self) -> (result: Scalar)
    ensures scalar_as_nat(&result) == scalar52_as_nat(self)
    ensures is_canonical_scalar(&result) }

The 27-step squaring chain (Fermat exponentiation) inside Scalar52::invert is
hidden behind its stub — CryptoProver already verified that sub-function.
-/
private def invertSeed : StrataDDM.Program :=
#strata
program Boole;

type Scalar;
type scalar52;

function scalar_as_nat(s: Scalar) : int;
function scalar52_as_nat(u: scalar52) : int;
function group_canonical(n: int) : int;
function is_canonical_scalar(s: Scalar) : bool;

procedure Impl__Scalar_unpack(self: Scalar) returns (result: scalar52)
spec {
  ensures scalar52_as_nat(result) == scalar_as_nat(self);
}
{
  assume false;
};

procedure Impl__Scalar52_invert(self: scalar52) returns (result: scalar52)
spec {
  ensures (scalar52_as_nat(self) > 0 ==>
    group_canonical(scalar52_as_nat(result) * scalar52_as_nat(self)) == 1);
}
{
  assume false;
};

procedure Impl__Scalar52_pack(self: scalar52) returns (result: Scalar)
spec {
  ensures scalar_as_nat(result) == scalar52_as_nat(self);
  ensures is_canonical_scalar(result);
}
{
  assume false;
};

procedure scalar_invert(s: Scalar) returns (result: Scalar)
spec {
  requires is_canonical_scalar(s);
  ensures (scalar_as_nat(s) > 0 ==>
    group_canonical(scalar_as_nat(result) * scalar_as_nat(s)) == 1);
  ensures is_canonical_scalar(result);
}
{
  var unpacked: scalar52;
  call unpacked := Impl__Scalar_unpack(s);
  var inv_unpacked: scalar52;
  call inv_unpacked := Impl__Scalar52_invert(unpacked);
  call result := Impl__Scalar52_pack(inv_unpacked);
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: Impl__Scalar_unpack_ensures_0_3161
Property: assert
Result: ✅ pass

Obligation: Impl__Scalar52_invert_ensures_2_3325
Property: assert
Result: ✅ pass

Obligation: Impl__Scalar52_pack_ensures_4_3544
Property: assert
Result: ✅ pass

Obligation: Impl__Scalar52_pack_ensures_5_3602
Property: assert
Result: ✅ pass

Obligation: scalar_invert_ensures_8_3767
Property: assert
Result: ✅ pass

Obligation: scalar_invert_ensures_9_3872
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" invertSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole invertSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
