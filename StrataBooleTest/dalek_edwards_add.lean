/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: Edwards point addition — group law on the Edwards curve
Source: dalek-lite `curve25519-dalek/src/edwards.rs`, `AddAssign` impl for `EdwardsPoint`

Security relevance:
  - Point addition is the core primitive for all scalar multiplication on
    Ed25519 and Ristretto. Every signing, verification, and DH operation
    reduces to repeated point additions. A wrong addition silently produces
    a point not on the curve, breaking every proof of security built on top.
  - First postcondition: result is well-formed (on the curve, affine Z ≠ 0).
  - Second postcondition: result's affine coordinates satisfy the Edwards
    group law.

Level 1 — Verus source (verbatim):

  impl<'b> AddAssign<&'b EdwardsPoint> for EdwardsPoint {
      fn add_assign(&mut self, _rhs: &'b EdwardsPoint)
          requires
              is_well_formed_edwards_point(*old(self)),
              is_well_formed_edwards_point(*_rhs),
          ensures
              is_well_formed_edwards_point(*self),
              ({
                  let (x1, y1) = edwards_point_as_affine(*old(self));
                  let (x2, y2) = edwards_point_as_affine(*_rhs);
                  edwards_point_as_affine(*self) == edwards_add(x1, y1, x2, y2)
              }),
      {
          *self = &*self + _rhs;
      }
  }
-/

/-
Level 2 — Boole encoding

`add_assign` body is a single call to the Add operator implementation.
The stub carries the two postconditions from the Verus ensures; after the
`call`, cvc5 assumes them and discharges the top-level spec directly.

Sub-function Verus postconditions (from dalek-lite edwards.rs):

  impl<'a, 'b> Add<&'b EdwardsPoint> for &'a EdwardsPoint -> (result: EdwardsPoint)
    ensures is_well_formed_edwards_point(result)
    ensures ({ let (x1,y1) = edwards_point_as_affine(*self);
               let (x2,y2) = edwards_point_as_affine(*rhs);
               edwards_point_as_affine(result) == edwards_add(x1,y1,x2,y2) })
-/
private def edwardsAddSeed : StrataDDM.Program :=
#strata
program Boole;

type EdwardsPoint;
type AffinePoint;

function affine_of(p: EdwardsPoint) : AffinePoint;
function edwards_add_affine(a1: AffinePoint, a2: AffinePoint) : AffinePoint;
function is_well_formed(p: EdwardsPoint) : bool;

procedure Impl__EdwardsPoint_add(self: EdwardsPoint, rhs: EdwardsPoint) returns (result: EdwardsPoint)
spec {
  requires is_well_formed(self);
  requires is_well_formed(rhs);
  ensures is_well_formed(result);
  ensures affine_of(result) == edwards_add_affine(affine_of(self), affine_of(rhs));
}
{
  assume false;
};

procedure edwards_point_add(p1: EdwardsPoint, p2: EdwardsPoint) returns (result: EdwardsPoint)
spec {
  requires is_well_formed(p1);
  requires is_well_formed(p2);
  ensures is_well_formed(result);
  ensures affine_of(result) == edwards_add_affine(affine_of(p1), affine_of(p2));
}
{
  call result := Impl__EdwardsPoint_add(p1, p2);
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: Impl__EdwardsPoint_add_ensures_2_2560
Property: assert
Result: ✅ pass

Obligation: Impl__EdwardsPoint_add_ensures_3_2594
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Impl__EdwardsPoint_add_requires_0_2495_3
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Impl__EdwardsPoint_add_requires_1_2528_4
Property: assert
Result: ✅ pass

Obligation: edwards_point_add_ensures_7_2866
Property: assert
Result: ✅ pass

Obligation: edwards_point_add_ensures_8_2900
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" edwardsAddSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole edwardsAddSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
