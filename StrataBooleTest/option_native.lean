/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.MetaVerifier

open Strata

/--!
# Native option test.

Covers:
- `option T` construction with `some(e)` and `none<T>`
- `isSome`
- `isNone`
- `get`
- `getOrElse`
- Intentionally failing case of `get(r)` for an unconstrained option

TODO:
  - Lean verification condition generation path for parameterized option/pair
-/
private def testOptionAndTuples : StrataDDM.Program :=

#strata

program Boole;

var o : option (pair int int);

procedure test_testers () returns (){
  var o_none : option int := none<int>;
  var o_some : option int := some(1);

  assert isSome(o_some) == true;
  assert isNone(o_none) == true;
  assert isSome(o_none) == false;
  assert isNone(o_none) == true;
};

procedure test_get () returns (){
  var o_some : option int := some(1);

  assert get(o_some) == 1;
  assert getOrElse(none<int>, 1) == 1;
};

procedure negative_get_test(r : option int) { var x : int := get(r); };

#end

/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_0_654
Property: assert
Result: ✅ pass

Obligation: assert_1_687
Property: assert
Result: ✅ pass

Obligation: assert_2_720
Property: assert
Result: ✅ pass

Obligation: assert_3_754
Property: assert
Result: ✅ pass

Obligation: assert_assert_4_864_calls_option.get_0
Property: assert
Result: ✅ pass

Obligation: assert_4_864
Property: assert
Result: ✅ pass

Obligation: assert_5_891
Property: assert
Result: ✅ pass

Obligation: init_calls_option.get_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" testOptionAndTuples (options := .quiet)



/- example : Strata.smtVCsCorrectBoole testOptionAndTuples := by
  gen_smt_vcs_boole
  all_goals (try grind)
 -/
