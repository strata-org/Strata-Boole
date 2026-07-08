/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# The Problem: Opaque-Sort Nat

With the old encoding (`type nat;`), `nat.toInt` is a pure uninterpreted
function — cvc5 has no structural definition to unfold. Two concrete problems:

1. **Large literals are expensive.** Proving `nat.toInt(nat.fromInt(1024)) == 1024`
   requires E-matching to fire 1024 times through the `nat_fromInt_pos` axiom.
   In unary this times out past ~200. Binary reduces that to 10 steps (log₂ 1024).

2. **No concrete term algebra.** With opaque `nat`, cvc5 cannot construct a
   specific `nat` value — there are no constructors. Reasoning is limited to
   what the bridge axioms can express via E-matching.

Fix: make `nat` an algebraic datatype whose term algebra IS ℕ.
`pos.toInt` emits as `define-fun-rec`, giving cvc5 a complete structural
definition it can unfold directly.

Note: SAT-direction queries return `unknown` in both encodings when
universally-quantified bridge axioms are present — that is a separate,
documented ceiling unrelated to this fix.
-/

-- ── Option A: Unary (Peano) ──────────────────────────────────────────────────
-- Terms grow linearly: nat.fromInt(n) = Succ(Succ(...(Zero())...)) — n levels.
-- Fine for small values; times out past ~200.

private def unary_example : StrataDDM.Program :=
#strata
program Boole;

datatype nat () { Zero(), Succ(pred: nat) };

rec function nat.toInt (@[cases] n : nat) : int {
  if nat..isZero(n) then 0 else 1 + nat.toInt(nat..pred(n))
};

function nat.fromInt (x : int) : nat;
axiom [nat_fromInt_zero]: nat.fromInt(0) == Zero();
axiom [nat_fromInt_pos]: forall x : int :: 1 <= x ==> nat.fromInt(x) == Succ(nat.fromInt(x - 1));

axiom [nat_nonneg]:        forall n : nat :: 0 <= nat.toInt(n);
axiom [nat_fromInt_toInt]: forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x;
axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;

// nat.fromInt(5) has term model Succ(Succ(Succ(Succ(Succ(Zero()))))) — 5 levels
procedure test_literal () returns ()
spec { ensures nat.toInt(nat.fromInt(5)) == 5; }
{ assert nat.toInt(nat.fromInt(5)) == 5; };

#end

/-- info:
Obligation: nat.toInt_body_calls_nat..pred_0
Property: assert
Result: ✅ pass

Obligation: nat.toInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: assert_1_2280
Property: assert
Result: ✅ pass

Obligation: test_literal_ensures_0_2236
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" unary_example (options := .quiet)

-- ── Option B: Binary (Coq's N / positive) ───────────────────────────────────
-- Terms grow logarithmically: nat.fromInt(1024) = Npos(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xH()))))))))))) — 10 levels.
-- nat.fromInt(2^31) ≈ 3 s; unary times out past 200.

private def binary_example : StrataDDM.Program :=
#strata
program Boole;

datatype pos () { xH(), xO(xO_h: pos), xI(xI_h: pos) };
datatype nat () { N0(), Npos(val: pos) };

rec function pos.toInt (@[cases] p : pos) : int {
  if pos..isxH(p) then 1
  else if pos..isxO(p) then 2 * pos.toInt(pos..xO_h(p))
  else 2 * pos.toInt(pos..xI_h(p)) + 1
};

function nat.toInt (n : nat) : int {
  if nat..isN0(n) then 0 else pos.toInt(nat..val(n))
}

function pos.fromInt (x : int) : pos;
axiom [pos_fromInt_base]: forall x : int :: x == 1 ==> pos.fromInt(x) == xH();
axiom [pos_fromInt_even]: forall x : int :: x > 1 && x mod 2 == 0 ==> pos.fromInt(x) == xO(pos.fromInt(x div 2));
axiom [pos_fromInt_odd]:  forall x : int :: x > 1 && x mod 2 != 0 ==> pos.fromInt(x) == xI(pos.fromInt(x div 2));

function nat.fromInt (x : int) : nat {
  if x <= 0 then N0() else Npos(pos.fromInt(x))
}

axiom [nat_nonneg]:        forall n : nat :: 0 <= nat.toInt(n);
axiom [nat_fromInt_toInt]: forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x;
axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;

// nat.fromInt(5) = Npos(xI(xO(xH()))) — depth 2, not 5
procedure test_literal () returns ()
spec { ensures nat.toInt(nat.fromInt(5)) == 5; }
{ assert nat.toInt(nat.fromInt(5)) == 5; };

// 1024 = 2^10 — depth 10 term vs 1024 in unary
procedure test_large_literal () returns ()
spec { ensures nat.toInt(nat.fromInt(1024)) == 1024; }
{ assert nat.toInt(nat.fromInt(1024)) == 1024; };

#end

/-- info:
Obligation: pos.toInt_body_calls_pos..xO_h_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_body_calls_pos..xI_h_1
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: nat.toInt_body_calls_nat..val_0
Property: assert
Result: ✅ pass

Obligation: assert_1_4289
Property: assert
Result: ✅ pass

Obligation: test_literal_ensures_0_4245
Property: assert
Result: ✅ pass

Obligation: assert_3_4482
Property: assert
Result: ✅ pass

Obligation: test_large_literal_ensures_2_4432
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" binary_example (options := .quiet)

-- ── Option C: natLibrary ─────────────────────────────────────────────────────
-- The binary nat above is packaged as `Strata.BooleNat.natLibrary` in
-- `StrataBoole.Nat`. Import that module and call `Strata.BooleNat.prepend`
-- to stitch it onto any user program. See StrataBooleTest/nat_binary_datatype.lean
-- for end-to-end verification of natLibrary.
