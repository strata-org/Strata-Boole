/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

def loopSimple : StrataDDM.Program :=
#strata
program Boole;

procedure loopSimple (n: int) returns (r: int)
spec {
  requires (n >= 0);
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(i < n)
    invariant (i <= n && ((i * (i-1)) div 2 == sum))
  {
    sum := sum + i;
    i := i + 1;
  }
  assert [sum_assert]: ((n * (n-1)) div 2 == sum);
  assert [neg_cond]: (i == n);
  r := sum;
};
#end

open Strata.SMT

theorem loopSimple_smtVCsCorrectBoole : smtVCsCorrectBoole loopSimple := by
  gen_smt_vcs_boole
  all_goals (try grind)

/-- info: 'loopSimple_smtVCsCorrectBoole' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound,
 loopSimple_smtVCsCorrectBoole._genSMTVCsBoole_tcbBridge_1_3,
 Core.WFFactory._native.native_decide.ax_1✝]-/
#guard_msgs in
#print axioms loopSimple_smtVCsCorrectBoole
