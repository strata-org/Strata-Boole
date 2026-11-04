/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

-- A local function is a local variable bound to a lambda: it may capture
-- variables in scope, and its parameters keep their declaration order.
private def local_functions :=
#strata
program Boole;

procedure local_fns(x : int) returns ()
spec { requires x == 1; }
{
  function addX(y : int) : int { y + x }
  function pick(a : int, b : bool, c : int) : int { if b then a else c }
  assert [addX_5]: addX(5) == 6;
  assert [pick_true]: pick(1, true, 2) == 1;
  assert [pick_false]: pick(1, false, 2) == 2;
};

#end

/--
info:
Obligation: addX_5
Property: assert
Result: ✅ pass

Obligation: pick_true
Property: assert
Result: ✅ pass

Obligation: pick_false
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" local_functions (options := .quiet)

-- A local function cannot have preconditions.
private def local_function_precondition :=
#strata
program Boole;

procedure p(x : int) returns ()
{
  function f(y : int) : int requires y > 0; { y }
  assert [f_1]: f(1) == 1;
};

#end

/-- error: local function 'f': preconditions are not supported -/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" local_function_precondition (options := .quiet)
