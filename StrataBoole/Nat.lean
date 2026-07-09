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

## Problem with opaque nat

The opaque-sort `nat` used in older benchmarks (`type nat;`) has a limitation:
cvc5 treats `nat_to_int` as a pure uninterpreted function, so every satisfying
assignment is an infinite abstract model and the solver returns `unknown` rather
than a concrete counterexample.

## Solution: algebraic datatype

Here `nat` is a *binary algebraic datatype* whose term algebra IS ℕ:

- `pos`: positive binary numbers (`xH = 1`, `xO(xO_h) = 2 * xO_h`, `xI(xI_h) = 2 * xI_h + 1`)
- `nat`: zero or a positive binary number (`N0 = 0`, `Npos(val) = val`)

`pos.toInt` is defined with a Boole `rec` block and emitted as `define-fun-rec`
in SMT-LIB, giving cvc5 a complete definition for both proof (UNSAT) and
counterexample (SAT) directions. `pos.fromInt` is an opaque uninterpreted function
with three case axioms for E-matching in the UNSAT direction. Three bridge axioms
are kept as hints for E-matching (they are valid theorems of the definitions).

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
// Structural recursion on pos via @[cases]. The SMT encoder emits this as
// define-fun-rec, giving cvc5 a complete definition for proofs and counterexamples.
rec
function pos.toInt (@[cases] p : pos) : int {
  if pos..isxH(p) then 1
  else if pos..isxO(p) then 2 * pos.toInt(pos..xO_h(p))
  else 2 * pos.toInt(pos..xI_h(p)) + 1
}
;

// ── nat.toInt ────────────────────────────────────────────────────────────────
// Non-recursive: delegates to pos.toInt for the Npos case.
function nat.toInt (n : nat) : int {
  if nat..isN0(n) then 0 else pos.toInt(nat..val(n))
}

// ── pos.fromInt ──────────────────────────────────────────────────────────────
// Recursive on x div 2; meaningful for x >= 1 (nat.fromInt guards x <= 0).
// `decreases x` generates two termination obligations (one per recursive branch):
//   x > 1 ==> x div 2 < x   — discharged by cvc5 as a trivial LIA fact.
// Emitted as define-fun-rec, so cvc5 has a complete definition for both
// proof (UNSAT) and counterexample (SAT) directions.
rec
function pos.fromInt (x : int) : pos
decreases x
{
  if x <= 1 then xH()
  else if x mod 2 == 0 then xO(pos.fromInt(x div 2))
  else xI(pos.fromInt(x div 2))
}
;

// ── nat.fromInt ──────────────────────────────────────────────────────────────
function nat.fromInt (x : int) : nat {
  if x <= 0 then N0() else Npos(pos.fromInt(x))
}

// ── Bridge axioms ────────────────────────────────────────────────────────────
axiom [nat_nonneg]:        forall n : nat :: 0 <= nat.toInt(n);
axiom [nat_fromInt_toInt]: forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x;
axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;

// ── Arithmetic operators ─────────────────────────────────────────────────────
function nat.add (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) + nat.toInt(b)) }
function nat.sub (a : nat, b : nat) : nat
  requires nat.toInt(b) <= nat.toInt(a);
{ nat.fromInt(nat.toInt(a) - nat.toInt(b)) }
function nat.mul (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) * nat.toInt(b)) }
// Precondition: b != N0(). SMT-LIB integer div/mod by zero is underspecified;
// callers must ensure the divisor is positive.
function nat.div (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) div nat.toInt(b)) }
function nat.mod (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) mod nat.toInt(b)) }
function nat.lt  (a : nat, b : nat) : bool { nat.toInt(a) <  nat.toInt(b) }
function nat.le  (a : nat, b : nat) : bool { nat.toInt(a) <= nat.toInt(b) }
function nat.gt  (a : nat, b : nat) : bool { nat.toInt(a) >  nat.toInt(b) }
function nat.ge  (a : nat, b : nat) : bool { nat.toInt(a) >= nat.toInt(b) }

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
