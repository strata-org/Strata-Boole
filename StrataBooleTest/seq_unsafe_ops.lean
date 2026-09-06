/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
Boole lowers Core's total (unsafe) sequence operations `Sequence.select!`,
`Sequence.update!`, `Sequence.take!`, `Sequence.drop!`.  Unlike the safe variants
they carry no bounds precondition; out of range they are unconstrained.  They are
the right operators inside spec functions over fixed-size arrays whose length is a
typing fact (e.g. a 32-byte scalar), where a bounds obligation per read would only
restate that fact.
-/

private def unsafeSeqSeed : StrataDDM.Program :=
#strata
program Boole;

function first_two(s: Sequence int) : int {
  Sequence.select!(s, 0) + 256 * Sequence.select!(s, 1)
}

procedure read_two(s: Sequence int) returns (r: int)
spec {
  requires Sequence.length(s) >= 2;
  requires Sequence.select!(s, 0) == 1;
  requires Sequence.select!(s, 1) == 2;
  ensures r == 513;
}
{
  r := first_two(s);
};

procedure write_keeps_length(s: Sequence int, v: int) returns (t: Sequence int)
spec {
  requires Sequence.length(s) >= 1;
  ensures Sequence.length(t) == Sequence.length(s);
}
{
  t := Sequence.update!(s, 0, v);
};

procedure split(s: Sequence int) returns (n: int)
spec {
  requires Sequence.length(s) >= 3;
  ensures n == 3;
}
{
  n := Sequence.length(Sequence.take!(s, 1)) + Sequence.length(Sequence.drop!(s, Sequence.length(s) - 2));
};
#end

/-- info:
Obligation: read_two_ensures_3_916
Property: assert
Result: ✅ pass

Obligation: write_keeps_length_ensures_5_1088
Property: assert
Result: ✅ pass

Obligation: split_ensures_7_1275
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" unsafeSeqSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole unsafeSeqSeed := by
  gen_smt_vcs_boole
  all_goals (try grind)
