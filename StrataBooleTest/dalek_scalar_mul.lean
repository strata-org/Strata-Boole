/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: scalar mul — scalar multiplication mod ℓ
Source: dalek-lite `curve25519-dalek/src/scalar.rs`, `MulAssign` impl for `Scalar`

Security relevance:
  - Scalar multiplication is the inner loop of every Ed25519 and Ristretto
    operation: signing, verification, DH. A wrong result corrupts everything
    that depends on it.
  - First postcondition: result represents (a × b) mod ℓ.
  - Second postcondition: result is canonical, i.e. in [0, ℓ).

Level 1 — Verus source (verbatim):

  impl<'a> MulAssign<&'a Scalar> for Scalar {
      fn mul_assign(&mut self, _rhs: &'a Scalar)
          requires
              is_canonical_scalar(old(self)),
              is_canonical_scalar(_rhs),
          ensures
              u8_32_as_group_canonical(self.bytes) ==
                  group_canonical(scalar_as_nat(&old(self)) * scalar_as_nat(_rhs)),
              is_canonical_scalar(self),
      {
          *self = &*self * _rhs;
      }
  }
-/

-- Level 2 — Boole encoding
-- `mul_fn` models the multiplication. Two axioms capture:
-- (1) the modular product equation, (2) canonical output.
-- cvc5 discharges both by instantiating each axiom with the arguments.
private def scalarMulSeed : StrataDDM.Program :=
#strata
program Boole;

type Scalar;

function mul_fn(a: Scalar, b: Scalar) : Scalar;
function scalar_as_nat(s: Scalar) : int;
function group_canonical(n: int) : int;
function is_canonical_scalar(s: Scalar) : bool;

axiom (∀ a: Scalar . ∀ b: Scalar . group_canonical(scalar_as_nat(mul_fn(a, b))) == group_canonical(scalar_as_nat(a) * scalar_as_nat(b)));
axiom (∀ a: Scalar . ∀ b: Scalar . is_canonical_scalar(mul_fn(a, b)));

procedure scalar_mul(a: Scalar, b: Scalar) returns (result: Scalar)
spec {
  requires is_canonical_scalar(a);
  requires is_canonical_scalar(b);
  ensures group_canonical(scalar_as_nat(result)) == group_canonical(scalar_as_nat(a) * scalar_as_nat(b));
  ensures is_canonical_scalar(result);
}
{
  result := mul_fn(a, b);
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: scalar_mul_ensures_4_1954
Property: assert
Result: ✅ pass

Obligation: scalar_mul_ensures_5_2060
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" scalarMulSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole scalarMulSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
