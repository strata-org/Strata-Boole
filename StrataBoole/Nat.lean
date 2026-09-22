/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole
import StrataDDM.Integration.Lean.HashCommands

/-!
# Binary Nat Library for Boole

Core-syntax specification of the nat library that `Strata.Boole.verify` injects
whenever a program uses `nat` or `pos`.  The implementation is `natCorePreamble`
in `StrataBoole/Verify.lean`; nothing imports this module.  Keep the two in
step.  Build with `lake build StrataBoole.Nat` (no other target does).

`pos`/`nat` are binary datatypes (term algebra ℕ) with a recursive `int` bridge;
`nat.toInt`, `nat.fromInt` and the operators are uninterpreted, characterised by
axioms.  Reasoning and measurements: the comments in `natCorePreamble` and
Strata-Boole #14.  Core has prefix integer operators (`int.add`, `int.le`, …),
hence the notation below.

## Usage

```lean
import StrataBoole.Nat

private def myProg : StrataDDM.Program :=
  Strata.BooleNat.prepend (#strata
  program Boole;
  -- nat, pos, nat.toInt, nat.fromInt, nat.add, … all available
  procedure uses_nat (n : nat) returns ()
  spec { ensures 0 <= nat.toInt(n); }
  { assert 0 <= nat.toInt(n); };
  #end)
```
-/

namespace Strata.BooleNat

public def natLibrary : StrataDDM.Program :=
#strata
program Core;

// ── Positive binary numbers ──────────────────────────────────────────────────
// Canonical representation: every positive integer has exactly one pos term.
// Field names must be unique per datatype in Boole, so xO and xI use
// distinct names xO_h and xI_h for their recursive pos children.
datatype pos () {
  xH(),            // 1
  xO(xO_h: pos),  // 2 * xO_h
  xI(xI_h: pos)   // 2 * xI_h + 1
};

// ── Natural numbers ──────────────────────────────────────────────────────────
datatype nat () {
  N0(),
  Npos(val: pos)
};

// ── pos.toInt ────────────────────────────────────────────────────────────────
// Structural recursion on pos via @[cases]; emitted as a UF with per-constructor
// axioms (define-fun-rec on request, Strata #1478).
rec
function pos.toInt (@[cases] p : pos) : int {
  if pos..isxH(p) then 1
  else if pos..isxO(p) then int.mul(2, pos.toInt(pos..xO_h(p)))
  else int.add(int.mul(2, pos.toInt(pos..xI_h(p))), 1)
}
;

// ── nat.toInt ────────────────────────────────────────────────────────────────
// No body: defined constructor-wise below (no case split on an opaque nat).
function nat.toInt (n : nat) : int;
axiom [nat_toInt_N0]:   nat.toInt(N0()) == 0;
axiom [nat_toInt_Npos]: forall p : pos :: nat.toInt(Npos(p)) == pos.toInt(p);

// ── pos.fromInt ──────────────────────────────────────────────────────────────
// Recursive on x div 2, meaningful for x >= 1 (nat.fromInt guards x <= 0);
// `decreases x` gives one termination obligation per branch.  Emitted like pos.toInt.
rec
function pos.fromInt (x : int) : pos
decreases x
{
  if int.le(x, 1) then xH()
  else if int.mod(x, 2) == 0 then xO(pos.fromInt(int.div(x, 2)))
  else xI(pos.fromInt(int.div(x, 2)))
}
;

// ── nat.fromInt ──────────────────────────────────────────────────────────────
// No body: must stay a symbol so the bridge-axiom triggers below match.
function nat.fromInt (x : int) : nat;
axiom [nat_fromInt_nonpos]: forall x : int :: int.le(x, 0) ==> nat.fromInt(x) == N0();
axiom [nat_fromInt_pos]:    forall x : int :: int.lt(0, x) ==> nat.fromInt(x) == Npos(pos.fromInt(x));

// ── Bridge axioms ────────────────────────────────────────────────────────────
axiom [nat_nonneg]:        forall n : nat :: int.le(0, nat.toInt(n));
axiom [nat_fromInt_toInt]: forall x : int :: int.le(0, x) ==> nat.toInt(nat.fromInt(x)) == x;
axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;

// ── Arithmetic operators ─────────────────────────────────────────────────────
// No bodies: one distribution law over nat.toInt each, guarded for sub/div/mod.
function nat.add (a : nat, b : nat) : nat;
axiom [nat_toInt_add]: forall a : nat, b : nat :: nat.toInt(nat.add(a, b)) == int.add(nat.toInt(a), nat.toInt(b));
// The implementation also puts `requires nat.toInt(b) <= nat.toInt(a)` on
// nat.sub; Core's bodiless-function syntax has no requires slot.
function nat.sub (a : nat, b : nat) : nat;
axiom [nat_toInt_sub]: forall a : nat, b : nat :: int.le(nat.toInt(b), nat.toInt(a)) ==> nat.toInt(nat.sub(a, b)) == int.sub(nat.toInt(a), nat.toInt(b));
function nat.mul (a : nat, b : nat) : nat;
axiom [nat_toInt_mul]: forall a : nat, b : nat :: nat.toInt(nat.mul(a, b)) == int.mul(nat.toInt(a), nat.toInt(b));
// SMT-LIB integer div/mod by zero is underspecified; the laws hold for b > 0 only.
function nat.div (a : nat, b : nat) : nat;
axiom [nat_toInt_div]: forall a : nat, b : nat :: int.lt(0, nat.toInt(b)) ==> nat.toInt(nat.div(a, b)) == int.div(nat.toInt(a), nat.toInt(b));
function nat.mod (a : nat, b : nat) : nat;
axiom [nat_toInt_mod]: forall a : nat, b : nat :: int.lt(0, nat.toInt(b)) ==> nat.toInt(nat.mod(a, b)) == int.mod(nat.toInt(a), nat.toInt(b));
function nat.lt  (a : nat, b : nat) : bool { int.lt(nat.toInt(a), nat.toInt(b)) }
function nat.le  (a : nat, b : nat) : bool { int.le(nat.toInt(a), nat.toInt(b)) }
function nat.gt  (a : nat, b : nat) : bool { int.gt(nat.toInt(a), nat.toInt(b)) }
function nat.ge  (a : nat, b : nat) : bool { int.ge(nat.toInt(a), nat.toInt(b)) }

#end

/-- Prepend the binary-nat library to any Boole program.

    Filters out the `program Boole;` declaration from `userProg` — the
    nat library's declaration serves as the single header.  All nat/pos
    datatypes, `toInt`/`fromInt`, bridge axioms, and arithmetic operators
    become available in `userProg`'s procedures and functions. -/
public def prepend (userProg : StrataDDM.Program) : StrataDDM.Program :=
  -- Strip the program header using the full qualified name to avoid accidentally
  -- dropping user-dialect ops that share the local name "programCommand".
  let userCmds := userProg.commands.filter
    (fun op => op.name.dialect != "StrataHeader" || op.name.name != "programCommand")
  -- Fold via addCommand so natLibrary's already-computed globalContext and
  -- dialect map are used as the base, avoiding a full re-traversal.
  userCmds.foldl (·.addCommand ·) natLibrary

end Strata.BooleNat
