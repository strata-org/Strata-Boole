/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: scalar invert — multiplicative inverse mod ℓ
Source: dalek-lite `curve25519-dalek/src/scalar.rs`, lines 1646–1684

Security relevance:
  - First postcondition: for nonzero s, s⁻¹ × s ≡ 1 (mod ℓ).
    A wrong invert silently corrupts Ed25519 signing and Ristretto batch ops.
  - Second postcondition: result stays in canonical range [0, ℓ).

Level 1 — Verus source (verbatim):

  pub fn invert(&self) -> (result: Scalar)
      requires
          is_canonical_scalar(self),
      ensures
          scalar_as_nat(self) > 0 ==> group_canonical(
              scalar_as_nat(&result) * scalar_as_nat(self),
          ) == 1,
          is_canonical_scalar(&result),
-/

-- Level 2 — Boole encoding
-- `invert_fn`, `scalar_as_nat`, `group_canonical`, `is_canonical_scalar`,
-- and `is_nonzero` are uninterpreted functions; their properties are axioms.
-- Implication in Boole is written `==>` (not `=>`).
private def invertSeed : StrataDDM.Program :=
#strata
program Boole;

type Scalar;

function invert_fn(s: Scalar) : Scalar;
function scalar_as_nat(s: Scalar) : int;
function group_canonical(n: int) : int;
function is_canonical_scalar(s: Scalar) : bool;
function is_nonzero(s: Scalar) : bool;

axiom (∀ s: Scalar . is_nonzero(s) ==> group_canonical(scalar_as_nat(invert_fn(s)) * scalar_as_nat(s)) == 1);
axiom (∀ s: Scalar . is_canonical_scalar(invert_fn(s)));

procedure scalar_invert(s: Scalar) returns (result: Scalar)
spec {
  requires is_canonical_scalar(s);
  ensures (is_nonzero(s) ==> group_canonical(scalar_as_nat(result) * scalar_as_nat(s)) == 1);
  ensures is_canonical_scalar(result);
}
{
  result := invert_fn(s);
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: scalar_invert_ensures_3_1643
Property: assert
Result: ✅ pass

Obligation: scalar_invert_ensures_4_1737
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" invertSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole invertSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
