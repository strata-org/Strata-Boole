/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/recursion`
- `vlir-tests:mutual_recursion`
- `vlir-tests:recursion`
- Verus link:
  `guide/recursion`: https://github.com/verus-lang/verus/blob/main/examples/guide/recursion.rs
-/

-- Working: mutual recursion over a Peano-style datatype.
-- `even` calls `odd` and vice versa; both terminate by structural recursion
-- on the `@[cases]` MyNat parameter.
private def mutualRecursionSeed : StrataDDM.Program :=
#strata
program Boole;

datatype MyNat () { Zero(), Succ(pred: MyNat) };

rec
function even(@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then true else odd(MyNat..pred(n))
}
function odd(@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then false else even(MyNat..pred(n))
}
;

procedure test_parity() returns ()
spec {
  ensures even(Zero()) == true;
  ensures odd(Zero()) == false;
  ensures even(Succ(Zero())) == false;
  ensures odd(Succ(Zero())) == true;
}
{
  assert even(Zero()) == true;
  assert odd(Zero()) == false;
  assert even(Succ(Zero())) == false;
  assert odd(Succ(Zero())) == true;
};
#end

/-- info:
Obligation: even_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: odd_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: even_terminates_0
Property: assert
Result: ✅ pass

Obligation: odd_terminates_0
Property: assert
Result: ✅ pass

Obligation: assert_4_1094
Property: assert
Result: ✅ pass

Obligation: assert_5_1125
Property: assert
Result: ✅ pass

Obligation: assert_6_1156
Property: assert
Result: ✅ pass

Obligation: assert_7_1194
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_0_950
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_1_982
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_2_1014
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_3_1053
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mutualRecursionSeed (options := .quiet)

-- Lean backend: since Strata's `Core.genVCs` runs the termination-check and
-- precondition-elimination phases (strata-org/Strata#1471), the termination and
-- selector well-formedness VCs above (`even_terminates_0`,
-- `even_body_calls_MyNat..pred_0`, ...) reach the SMT→Lean bridge.  The bridge
-- now declares each datatype the query uses as a Lean inductive with its
-- testers and selectors (`Strata.SMT.DT.MyNat`), so those VCs become goals
-- about `MyNat` itself: its two constructors are exhaustive, and a selector's
-- result ranks below the constructor it came from.  Case analysis settles them;
-- `grind` does not, since to it the testers and selectors are opaque.
example : Strata.smtVCsCorrectBoole mutualRecursionSeed := by
  gen_smt_vcs_boole
  all_goals (try grind)
  all_goals
    (intro n; intros
     cases n <;>
       simp_all [Strata.SMT.DT.MyNat.is_Zero, Strata.SMT.DT.MyNat.is_Succ,
                 Strata.SMT.DT.MyNat.pred])

/-
Mutual recursion over int (#1167):
- `decreases n` on each function in the `rec` block; the termination VCs
  (`even_terminates_*`, `odd_terminates_*`) are discharged by cvc5.

Open gap — unfolding (Gap #1 / opaque+reveal):
- `even` and `odd` are emitted as uninterpreted functions (UFs) in the SMT
  query.  The solver knows their types and that they terminate, but not what
  they return at any specific argument.  Proving `even(1) == false` requires
  the defining equations as SMT assertions — blocked by Gap #1 (`opaque`/`reveal`).
-/
private def mutualRecursionIntSeed : StrataDDM.Program :=
#strata
program Boole;

rec
function even(n: int) : bool
  decreases n
{
  if n <= 0 then true else odd(n - 1)
}
function odd(n: int) : bool
  decreases n
{
  if n <= 0 then false else even(n - 1)
}
;
#end

/-- info:
Obligation: even_terminates_0
Property: assert
Result: ✅ pass

Obligation: even_terminates_1
Property: assert
Result: ✅ pass

Obligation: odd_terminates_0
Property: assert
Result: ✅ pass

Obligation: odd_terminates_1
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mutualRecursionIntSeed (options := .quiet)
