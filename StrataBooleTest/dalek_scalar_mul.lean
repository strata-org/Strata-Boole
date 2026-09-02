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

/-
Level 2 — Boole encoding

`mul_assign` body is a single call to the Mul operator implementation.
The stub carries the two postconditions from the Verus ensures; after the
`call`, cvc5 assumes them and discharges the top-level spec directly.

Sub-function Verus postconditions (from dalek-lite scalar.rs):

  impl<'a, 'b> Mul<&'b Scalar> for &'a Scalar -> (result: Scalar)
    ensures u8_32_as_group_canonical(result.bytes) ==
              group_canonical(scalar_as_nat(self) * scalar_as_nat(rhs))
    ensures is_canonical_scalar(&result)
-/
private def scalarMulSeed : StrataDDM.Program :=
#strata
program Boole;

type Scalar;

function scalar_as_nat(s: Scalar) : int;
function group_canonical(n: int) : int;
function is_canonical_scalar(s: Scalar) : bool;

procedure Impl__Scalar_mul(self: Scalar, rhs: Scalar) returns (result: Scalar)
spec {
  requires is_canonical_scalar(self);
  requires is_canonical_scalar(rhs);
  ensures group_canonical(scalar_as_nat(result)) == group_canonical(scalar_as_nat(self) * scalar_as_nat(rhs));
  ensures is_canonical_scalar(result);
}
{
  assume false;
};

procedure scalar_mul(a: Scalar, b: Scalar) returns (result: Scalar)
spec {
  requires is_canonical_scalar(a);
  requires is_canonical_scalar(b);
  ensures group_canonical(scalar_as_nat(result)) == group_canonical(scalar_as_nat(a) * scalar_as_nat(b));
  ensures is_canonical_scalar(result);
}
{
  call result := Impl__Scalar_mul(a, b);
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: Impl__Scalar_mul_ensures_2_2027
Property: assert
Result: ✅ pass

Obligation: Impl__Scalar_mul_ensures_3_2138
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Impl__Scalar_mul_requires_0_1952_3
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Impl__Scalar_mul_requires_1_1990_4
Property: assert
Result: ✅ pass

Obligation: scalar_mul_ensures_7_2346
Property: assert
Result: ✅ pass

Obligation: scalar_mul_ensures_8_2452
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" scalarMulSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole scalarMulSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
