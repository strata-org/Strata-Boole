/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# Nat as a Binary Algebraic Datatype with Recursive Int Bridge

Implements the design: "nat as a binary datatype with a recursive int bridge".

Problem with the opaque-sort nat (current benchmarks): bridge axioms make
`nat.toInt` an injection onto ℕ — every model is infinite, so cvc5 answers
`unknown` on satisfiable VCs and cannot exhibit a counterexample.

Fix: make `nat` an algebraic datatype whose term algebra IS ℕ. `nat.toInt`
becomes `define-fun-rec` (via Boole `rec`) at the SMT level — solvers can
construct concrete term models and return candidate counterexamples.

---

## Option A — Unary (Peano)

Counter-model terms grow linearly in the value; fine for small magnitudes.
-/

private def nat_unary_program : StrataDDM.Program :=
#strata
program Boole;

datatype nat () {
  Zero(),
  Succ(pred: nat)
};

// nat.toInt: structural recursion on nat — terminates via @[cases]
// → emitted as define-fun-rec in SMT → concrete term models
rec
function nat.toInt (@[cases] n : nat) : int {
  if nat..isZero(n) then 0 else 1 + nat.toInt(nat..pred(n))
}
;

// nat.fromInt: well-founded recursion on int — opaque + axioms to avoid
// the integer termination problem, while still giving E-matching for unsat.
function nat.fromInt (x : int) : nat;
axiom [nat_fromInt_zero]: nat.fromInt(0) == Zero();
axiom [nat_fromInt_pos]: forall x : int :: 1 <= x ==> nat.fromInt(x) == Succ(nat.fromInt(x - 1));

// Three shared axioms (valid theorems of the definitions; kept for E-matching)
axiom [nat_nonneg]:        forall n : nat :: 0 <= nat.toInt(n);
axiom [nat_fromInt_toInt]: forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x;
axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;

// Operator surface — identical to the opaque design
function nat.add (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) + nat.toInt(b)) }
function nat.sub (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) - nat.toInt(b)) }
function nat.mul (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) * nat.toInt(b)) }
function nat.div (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) div nat.toInt(b)) }
function nat.mod (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) mod nat.toInt(b)) }
function nat.lt  (a : nat, b : nat) : bool { nat.toInt(a) <  nat.toInt(b) }
function nat.le  (a : nat, b : nat) : bool { nat.toInt(a) <= nat.toInt(b) }
function nat.gt  (a : nat, b : nat) : bool { nat.toInt(a) >  nat.toInt(b) }
function nat.ge  (a : nat, b : nat) : bool { nat.toInt(a) >= nat.toInt(b) }

procedure test_nonneg (n : nat) returns ()
spec { ensures 0 <= nat.toInt(n); }
{ assert 0 <= nat.toInt(n); };

procedure test_add_comm (a : nat, b : nat) returns ()
spec { ensures nat.toInt(nat.add(a, b)) == nat.toInt(nat.add(b, a)); }
{ assert nat.toInt(nat.add(a, b)) == nat.toInt(nat.add(b, a)); };

procedure test_fromInt_roundtrip (x : int) returns ()
spec {
  requires 0 <= x;
  ensures nat.toInt(nat.fromInt(x)) == x;
}
{ assert nat.toInt(nat.fromInt(x)) == x; };

// Literal: nat.fromInt(5) has concrete term model Succ^5(Zero())
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

Obligation: assert_1_2745
Property: assert
Result: ✅ pass

Obligation: test_nonneg_ensures_0_2714
Property: assert
Result: ✅ pass

Obligation: assert_3_2902
Property: assert
Result: ✅ pass

Obligation: test_add_comm_ensures_2_2836
Property: assert
Result: ✅ pass

Obligation: assert_6_3093
Property: assert
Result: ✅ pass

Obligation: test_fromInt_roundtrip_ensures_5_3049
Property: assert
Result: ✅ pass

Obligation: assert_8_3290
Property: assert
Result: ✅ pass

Obligation: test_literal_ensures_7_3246
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_unary_program (options := .quiet)

/-!
## Option B — Binary (Coq's N / positive) — the default

Counter-model term depth O(log₂ value) vs O(value) for unary.
Binary nat: `nat.fromInt(2^31)` produces a depth-31 term in ~3 s;
unary times out past 200.

Field names must be unique per datatype in Boole, so `xO` and `xI`
use distinct names `xO_h` and `xI_h` for their `pos` children.
-/

private def nat_binary_program : StrataDDM.Program :=
#strata
program Boole;

// Positive binary numbers (canonical: each positive integer has exactly one term)
datatype pos () {
  xH(),           // 1
  xO(xO_h: pos), // 2 * xO_h
  xI(xI_h: pos)  // 2 * xI_h + 1
};

// Nat = 0 | positive binary
datatype nat () {
  N0(),
  Npos(val: pos)
};

// pos.toInt: structural recursion on pos — terminates via @[cases]
// → emitted as define-fun-rec → concrete term models
rec
function pos.toInt (@[cases] p : pos) : int {
  if pos..isxH(p) then 1
  else if pos..isxO(p) then 2 * pos.toInt(pos..xO_h(p))
  else 2 * pos.toInt(pos..xI_h(p)) + 1
}
;

// nat.toInt: non-recursive (delegates to pos.toInt)
function nat.toInt (n : nat) : int {
  if nat..isN0(n) then 0 else pos.toInt(nat..val(n))
}

// pos.fromInt: opaque UF + axioms; only meaningful for x >= 1.
function pos.fromInt (x : int) : pos;
axiom [pos_fromInt_base]: forall x : int :: x == 1 ==> pos.fromInt(x) == xH();
axiom [pos_fromInt_even]: forall x : int :: x > 1 && x mod 2 == 0 ==> pos.fromInt(x) == xO(pos.fromInt(x div 2));
axiom [pos_fromInt_odd]:  forall x : int :: x > 1 && x mod 2 != 0 ==> pos.fromInt(x) == xI(pos.fromInt(x div 2));

// nat.fromInt: non-recursive wrapper
function nat.fromInt (x : int) : nat {
  if x <= 0 then N0() else Npos(pos.fromInt(x))
}

// Three shared axioms
axiom [nat_nonneg]:        forall n : nat :: 0 <= nat.toInt(n);
axiom [nat_fromInt_toInt]: forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x;
axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;

// Operator surface
function nat.add (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) + nat.toInt(b)) }
function nat.sub (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) - nat.toInt(b)) }
function nat.mul (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) * nat.toInt(b)) }
function nat.div (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) div nat.toInt(b)) }
function nat.mod (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) mod nat.toInt(b)) }
function nat.lt  (a : nat, b : nat) : bool { nat.toInt(a) <  nat.toInt(b) }
function nat.le  (a : nat, b : nat) : bool { nat.toInt(a) <= nat.toInt(b) }
function nat.gt  (a : nat, b : nat) : bool { nat.toInt(a) >  nat.toInt(b) }
function nat.ge  (a : nat, b : nat) : bool { nat.toInt(a) >= nat.toInt(b) }

procedure test_nonneg (n : nat) returns ()
spec { ensures 0 <= nat.toInt(n); }
{ assert 0 <= nat.toInt(n); };

procedure test_add_comm (a : nat, b : nat) returns ()
spec { ensures nat.toInt(nat.add(a, b)) == nat.toInt(nat.add(b, a)); }
{ assert nat.toInt(nat.add(a, b)) == nat.toInt(nat.add(b, a)); };

procedure test_fromInt_roundtrip (x : int) returns ()
spec {
  requires 0 <= x;
  ensures nat.toInt(nat.fromInt(x)) == x;
}
{ assert nat.toInt(nat.fromInt(x)) == x; };

// Literal: nat.fromInt(5) = Npos(xI(xO(xH()))) — depth 2, not 5
procedure test_literal () returns ()
spec { ensures nat.toInt(nat.fromInt(5)) == 5; }
{ assert nat.toInt(nat.fromInt(5)) == 5; };

// Large literal: 1024 = 2^10 — depth 10 term vs 1024 in unary
procedure test_large_literal () returns ()
spec { ensures nat.toInt(nat.fromInt(1024)) == 1024; }
{ assert nat.toInt(nat.fromInt(1024)) == 1024; };

// SAT direction: these are satisfiable but not universally true.
// cvc5 returns unknown — expected, because the three bridge axioms are
// universally quantified and block concrete model search. This is the
// known ceiling with quantified axioms over an infinite domain.
procedure test_sat_exists_sum (a : nat, b : nat) returns ()
spec { ensures nat.toInt(a) + nat.toInt(b) == 7; }
{ assert nat.toInt(a) + nat.toInt(b) == 7; };

procedure test_sat_lt (a : nat, b : nat) returns ()
spec { ensures nat.toInt(a) < nat.toInt(b); }
{ assert nat.toInt(a) < nat.toInt(b); };

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

Obligation: assert_1_6926
Property: assert
Result: ✅ pass

Obligation: test_nonneg_ensures_0_6895
Property: assert
Result: ✅ pass

Obligation: assert_3_7083
Property: assert
Result: ✅ pass

Obligation: test_add_comm_ensures_2_7017
Property: assert
Result: ✅ pass

Obligation: assert_6_7274
Property: assert
Result: ✅ pass

Obligation: test_fromInt_roundtrip_ensures_5_7230
Property: assert
Result: ✅ pass

Obligation: assert_8_7472
Property: assert
Result: ✅ pass

Obligation: test_literal_ensures_7_7428
Property: assert
Result: ✅ pass

Obligation: assert_10_7680
Property: assert
Result: ✅ pass

Obligation: test_large_literal_ensures_9_7630
Property: assert
Result: ✅ pass

Obligation: assert_12_8118
Property: assert
Result: ❓ unknown

Obligation: test_sat_exists_sum_ensures_11_8072
Property: assert
Result: ❓ unknown

Obligation: assert_14_8263
Property: assert
Result: ❓ unknown

Obligation: test_sat_lt_ensures_13_8222
Property: assert
Result: ❓ unknown-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" nat_binary_program (options := .quiet)

/-!
## Option C — Native preamble injection

With `import StrataBoole.Nat`, a `#strata program Boole;` block automatically
has `pos`, `nat`, `nat.toInt`, `nat.fromInt`, bridge axioms, and arithmetic
operators in scope — no explicit declarations needed.
See `StrataBooleTest/nat_native.lean` for end-to-end verification.
-/
