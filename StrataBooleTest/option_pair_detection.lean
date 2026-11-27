/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# Pair and Option Injection Detection Tests

Verifies that `coreProgUsesDt` correctly detects option and pair usage in code paths:

Each test procedure has `int`-only header types and no nat in assert bodies so
that, if a fix is reverted, datatype detection returns false, the option/pair
library is not injected, the required sort or constructors are undefined in
the SMT encoding, and the test fails. This provides regression coverage for
every detection path.
-/

/-!
# OPTION
-/

-- 01 option ops only in if then else condition
private def opt_ite_cond_prog : StrataDDM.Program :=
#strata
program Boole;

procedure opt_ite_cond () returns (r : int)
spec { ensures r >= 0;}
{
  if (isSome(some(1))) {r := 1;} else {r := 0;}
};

#end
/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: opt_ite_cond_ensures_0_795
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" opt_ite_cond_prog (options := .quiet)


-- 02 option ops only in loop invariant
private def opt_loop_inv_prog : StrataDDM.Program :=
#strata
program Boole;

procedure opt_loop_inv (n : int) returns ()
spec { requires 0 <= n; }
{
  var i : int := 0;
  while (i < n)
    invariant isSome(some(0))
  { i := i + 1; }
};

#end
/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" opt_loop_inv_prog (options := .quiet)


-- 03 option ops only quantor body
private def opt_quant_body_prog : StrataDDM.Program :=
#strata
program Boole;

procedure opt_quant_body () returns ()
spec { ensures ∀ x:int . isSome(some(x)); }
{};

#end
/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: opt_quant_body_ensures_0_2133
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" opt_quant_body_prog (options := .quiet)


-- 04 option ops only in quantor binder
private def opt_quant_binder_prog : StrataDDM.Program :=
#strata
program Boole;

procedure opt_quant_binder () returns ()
spec { ensures ∀ o:option int . true; }
{};

#end
/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: opt_quant_binder_ensures_0_2702
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" opt_quant_binder_prog (options := .quiet)


-- 05 option ops only in variable initialization
private def opt_init_prog : StrataDDM.Program :=
#strata
program Boole;

procedure opt_init_only () returns (r : int)
spec { ensures r == 1; }
{
  var x : int := get(some(1));
  r := x;
};

#end
/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: init_calls_option.get_0
Property: assert
Result: ✅ pass

Obligation: opt_init_only_ensures_0_3276
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" opt_init_prog (options := .quiet)


-- 06 option ops only in precondition
private def opt_pre_prog : StrataDDM.Program :=
#strata
program Boole;

procedure opt_pre_only (x : int) returns ()
spec { requires isSome(some(x)); }
{};

#end
/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" opt_pre_prog (options := .quiet)


/-!
# PAIR
-/

-- 01 pair ops only in if then else condition
private def pair_ite_cond_prog : StrataDDM.Program :=
#strata
program Boole;

procedure pair_ite_cond () returns (r : int)
spec { ensures r >= 0;}
{
  if (isPair((1, 1))) {r := 1;} else {r := -1;}
};
#end
/--
info:
Obligation: pair_ite_cond_ensures_0_4418
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" pair_ite_cond_prog (options := .quiet)


-- 02 pair ops only in loop invariant
private def pair_loop_inv_prog : StrataDDM.Program :=
#strata
program Boole;

procedure pair_loop_inv (n : int) returns ()
spec { requires 0 <= n; }
{
  var i : int := 0;
  while (i < n)
    invariant isPair((1, 2))
  { i := i + 1; }
};

#end
/--
info:
Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" pair_loop_inv_prog (options := .quiet)


-- 03 pair ops only quantor body
private def pair_quant_body_prog : StrataDDM.Program :=
#strata
program Boole;

procedure pair_quant_body () returns ()
spec { ensures ∀ x:int . isPair((x, x)); }
{};

#end
/--
info:
Obligation: pair_quant_body_ensures_0_5414
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" pair_quant_body_prog (options := .quiet)


-- 04 pair ops only in quantor binder
private def pair_quant_binder_prog : StrataDDM.Program :=
#strata
program Boole;

procedure pair_quant_binder () returns ()
spec { ensures ∀ o: pair int int . true; }
{};

#end
/--
info:
Obligation: pair_quant_binder_ensures_0_5812
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" pair_quant_binder_prog (options := .quiet)


-- 05 pair ops only in variable initialization
private def pair_init_prog : StrataDDM.Program :=
#strata
program Boole;

procedure pair_init_only () returns (r : int)
spec { ensures r == 1; }
{
  var x : int := fst((1, 3));
  r := x;
};

#end
/--
info:
Obligation: pair_init_only_ensures_0_6219
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" pair_init_prog (options := .quiet)



/-!
# NEGATIVE
-/
private def neg_int_prog : StrataDDM.Program :=
#strata
program Boole;

procedure neg_int_only (x : int) returns (r : int)
spec { ensures r == x + 1; }
{ r := x + 1; };

#end
/--
info:
Obligation: neg_int_only_ensures_0_6611
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" neg_int_prog (options := .quiet)



private def neg_lookalike_prog : StrataDDM.Program :=
#strata
program Boole;

function option_pair_isSome_int (x : int) : bool;

procedure neg_lookalike (x : int) returns ()
{
  assume option_pair_isSome_int(x);
};

#end
/--
info:
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" neg_lookalike_prog (options := .quiet)


private def neg_global_def : StrataDDM.Program :=
#strata
program Boole;

datatype option () { None(), Some(val : int)};

procedure option_neg_global_def (x : int) returns ()
{
  assume option..isSome(Some(2));
};

#end
/--
info:
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" neg_global_def (options := .quiet)
