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

-- Level 2 — Boole encoding
-- `EdwardsPoint` and `AffinePoint` are uninterpreted types.
-- `affine_of` projects an extended Edwards point to affine coordinates.
-- `edwards_add_fn` models the internal point-addition algorithm; its result
-- is axiomatized against `affine_of` and `edwards_add_affine` (the spec-level
-- Edwards group law), matching the structure the verus-boogie translator would
-- emit for functions whose body delegates to a lower-level UF.
private def edwardsAddSeed : StrataDDM.Program :=
#strata
program Boole;

type EdwardsPoint;
type AffinePoint;

function edwards_add_fn(p1: EdwardsPoint, p2: EdwardsPoint) : EdwardsPoint;
function affine_of(p: EdwardsPoint) : AffinePoint;
function edwards_add_affine(a1: AffinePoint, a2: AffinePoint) : AffinePoint;
function is_well_formed(p: EdwardsPoint) : bool;

axiom (∀ p1: EdwardsPoint . ∀ p2: EdwardsPoint . is_well_formed(edwards_add_fn(p1, p2)));
axiom (∀ p1: EdwardsPoint . ∀ p2: EdwardsPoint . affine_of(edwards_add_fn(p1, p2)) == edwards_add_affine(affine_of(p1), affine_of(p2)));

procedure edwards_point_add(p1: EdwardsPoint, p2: EdwardsPoint) returns (result: EdwardsPoint)
spec {
  requires is_well_formed(p1);
  requires is_well_formed(p2);
  ensures is_well_formed(result);
  ensures affine_of(result) == edwards_add_affine(affine_of(p1), affine_of(p2));
}
{
  result := edwards_add_fn(p1, p2);
};
#end

-- Level 3 — Lean backend
/-- info:
Obligation: edwards_point_add_ensures_4_2682
Property: assert
Result: ✅ pass

Obligation: edwards_point_add_ensures_5_2716
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" edwardsAddSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole edwardsAddSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
