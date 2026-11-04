/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

-- `axiom` and `lemma` with a parameter list stand for a `forall` over the
-- parameters. A lemma is checked under the axioms declared before it, so
-- the same statement fails before `f_pos` and holds after it.
private def lemmas_and_axioms :=
#strata
program Boole;

function f(x : int) : int;

lemma [f_ge_one_before] (x : int): f(x) >= 1;

axiom [f_pos] (x : int): f(x) > 0;

lemma [f_ge_one] (x : int): f(x) >= 1;
lemma [f_zero]: f(0) > 0;

#end

/--
info:
Obligation: f_ge_one_before
Property: assert
Result: ❌ fail

Obligation: f_ge_one
Property: assert
Result: ✅ pass

Obligation: f_zero
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" lemmas_and_axioms (options := .quiet)
