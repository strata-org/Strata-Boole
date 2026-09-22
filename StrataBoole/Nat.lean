/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole
import StrataDDM.Integration.Lean.HashCommands

/-!
# Binary Nat Library for Boole

Provides `Strata.BooleNat.prepend` — injects a binary-nat datatype and
arithmetic library into any Boole program.

## Status: specification, not implementation

This file is the readable, Core-syntax **spec** of the nat library.  The
implementation is `natCorePreamble` in `StrataBoole/Verify.lean`, which builds
the same declarations programmatically and which `Strata.Boole.verify` injects
automatically whenever a program uses `nat` or `pos`.  Nothing in the
implementation imports this file; keep the two in sync by hand.  It is written
in Core, whose grammar has prefix integer operators (`int.add`, `int.le`, …) and
no infix arithmetic; build it with `lake build StrataBoole.Nat` — nothing else
builds it, so a stale spec goes unnoticed otherwise.

## Problem with opaque nat

The opaque-sort `nat` used in older benchmarks (`type nat;`) has a limitation:
cvc5 treats `nat_to_int` as a pure uninterpreted function, so every satisfying
assignment is an infinite abstract model and the solver returns `unknown` rather
than a concrete counterexample.

## Solution: algebraic datatype

Here `nat` is a *binary algebraic datatype* whose term algebra IS ℕ:

- `pos`: positive binary numbers (`xH = 1`, `xO(xO_h) = 2 * xO_h`, `xI(xI_h) = 2 * xI_h + 1`)
- `nat`: zero or a positive binary number (`N0 = 0`, `Npos(val) = val`)

`pos.toInt` and `pos.fromInt` are defined with Boole `rec` blocks. The Strata SMT
encoder currently emits recursive functions as uninterpreted functions (UF) with
per-constructor axioms, NOT as `define-fun-rec`. This means cvc5 cannot evaluate
them on constructor terms during model search, so constrained nat arithmetic (e.g.
`toInt(a) = 73`) returns `unknown` instead of a concrete counterexample. Three bridge
axioms are kept as E-matching hints (they are valid theorems of the definitions).

## Why `nat.toInt`, `nat.fromInt` and the arithmetic operators have no bodies

A function *with* a body is inlined by Strata everywhere it is used, like a
macro.  For these functions that was expensive (measured on dalek
`sum_of_slice`, 3 of 44 obligations timed out even at 6x the budget):

- `nat.toInt`'s body looks inside its argument ("is it `N0`? otherwise take the
  `pos` out of `Npos`").  Inlined at a call on a variable, that forces the solver
  to case-split on the variable's constructor at every use — ~47,000 splits per
  obligation, starving the quantifier engine.
- `nat.add(a, b)` as `nat.fromInt(nat.toInt(a) + nat.toInt(b))` makes every `+`
  a detour through `int` and back, and the solver must show the detour is
  harmless (non-negative) each time — ~2,000 such steps on a 32-term byte sum.

So they are declared without bodies and defined by axioms instead: `nat.toInt`
and `nat.fromInt` constructor-wise (`N0`/`Npos`, `x <= 0`/`x > 0`), and each
operator by one distribution law `nat.toInt(op(a, b)) == nat.toInt(a) <op>
nat.toInt(b)`.  An axiom only fires when its pattern appears, so `nat.toInt(x)`
on a variable triggers nothing, and a `+` is one step.  Both `nat.toInt` and
`nat.fromInt` must stay symbols: inlining `nat.fromInt` alone rewrites
`nat.toInt(nat.fromInt(x))` into `nat.toInt(if … )` and the bridge axiom
`nat_fromInt_toInt` no longer matches.

This is conservative: every axiom is a theorem of the body it replaces, and the
old bodies are a model of the axioms.  Result on `sum_of_slice`: 43/43, the
loop-invariant goal from timeout (30 s) to unsat in 3.6 s.

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
// Structural recursion on pos via @[cases]. Currently emitted by the Strata SMT
// encoder as a UF (declare-fun) with per-constructor axioms — NOT define-fun-rec.
// To get concrete counterexamples for constrained nat arithmetic, the encoder
// would need to emit this as define-fun-rec (pending Strata team opt-in support).
rec
function pos.toInt (@[cases] p : pos) : int {
  if pos..isxH(p) then 1
  else if pos..isxO(p) then int.mul(2, pos.toInt(pos..xO_h(p)))
  else int.add(int.mul(2, pos.toInt(pos..xI_h(p))), 1)
}
;

// ── nat.toInt ────────────────────────────────────────────────────────────────
// No body (see the header): defined constructor-wise, so it never forces a
// case split on an opaque nat.
function nat.toInt (n : nat) : int;
axiom [nat_toInt_N0]:   nat.toInt(N0()) == 0;
axiom [nat_toInt_Npos]: forall p : pos :: nat.toInt(Npos(p)) == pos.toInt(p);

// ── pos.fromInt ──────────────────────────────────────────────────────────────
// Recursive on x div 2; meaningful for x >= 1 (nat.fromInt guards x <= 0).
// `decreases x` generates two termination obligations (one per recursive branch):
//   x > 1 ==> x div 2 < x   — discharged by cvc5 as a trivial LIA fact.
// Currently emitted as UF + per-constructor axioms — NOT define-fun-rec.
// Same constraint as pos.toInt above.
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
// No body: must stay a symbol so the bridge axioms below keep their triggers.
function nat.fromInt (x : int) : nat;
axiom [nat_fromInt_nonpos]: forall x : int :: int.le(x, 0) ==> nat.fromInt(x) == N0();
axiom [nat_fromInt_pos]:    forall x : int :: int.lt(0, x) ==> nat.fromInt(x) == Npos(pos.fromInt(x));

// ── Bridge axioms ────────────────────────────────────────────────────────────
axiom [nat_nonneg]:        forall n : nat :: int.le(0, nat.toInt(n));
axiom [nat_fromInt_toInt]: forall x : int :: int.le(0, x) ==> nat.toInt(nat.fromInt(x)) == x;
axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;

// ── Arithmetic operators ─────────────────────────────────────────────────────
// No bodies: each is characterised by one distribution law over nat.toInt
// (guarded where the int result could be negative or the divisor zero).
function nat.add (a : nat, b : nat) : nat;
axiom [nat_toInt_add]: forall a : nat, b : nat :: nat.toInt(nat.add(a, b)) == int.add(nat.toInt(a), nat.toInt(b));
// The implementation additionally puts `requires nat.toInt(b) <= nat.toInt(a)`
// on nat.sub, so every call site proves it; Core's text syntax has no
// bodyless-function-with-requires form, so the spec carries the guard on the
// axiom only.
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
