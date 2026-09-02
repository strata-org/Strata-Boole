/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
Regression test: a callee that both `modifies` an array-typed global and takes
a plain `int` input referenced in its `ensures` clause, called from a procedure
that also passes the array as an `inout` argument.
-/

namespace Strata

private def quickSort :=
#strata
program Boole;

var A: Map int int;

procedure Quicksort(p: int, r: int) returns ()
spec
{
  requires p >= 1;
  requires r >= p;
  modifies A;
}
{
  if (p < r) {
    var q: int;
    call q := Partition(p, r);
    if (p < q) {
        call Quicksort(p, q - 1);
    }
    if (q < r) {
        call Quicksort(q + 1, r);
    }
  }
};

procedure Partition(p: int, r: int) returns (q: int)
spec
{
  requires p >= 1;
  requires r >= p;
  modifies A;
  ensures q >= p;
  ensures q <= r;
}
{
  var x: int;
  var i: int;
  var temp: int;
  var temp2: int;

  x := A[r];
  i := p - 1;

  for j:int := p to r - 1
    invariant p - 1 <= i
    invariant i < j
    invariant j <= r
  {
    if (A[j] <= x) {
      i := i + 1;
      temp := A[i];
      A := A[i := A[j]];
      A := A[j := temp];
    }
  }

  temp2 := A[i + 1];
  A[i+1] := A[r];
  A[r] := temp2;

  q := i + 1;
};

#end

theorem quickSort_smtVCsCorrect : Strata.smtVCsCorrectBoole quickSort := by
  gen_smt_vcs_boole
  all_goals (first | omega | trivial | grind)

end Strata
