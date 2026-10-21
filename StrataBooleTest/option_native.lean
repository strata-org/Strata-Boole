import StrataBoole.MetaVerifier

open Strata

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

Obligation: assert_0_278
Property: assert
Result: ✅ pass

Obligation: assert_1_311
Property: assert
Result: ✅ pass

Obligation: assert_2_344
Property: assert
Result: ✅ pass

Obligation: assert_3_378
Property: assert
Result: ✅ pass

Obligation: assert_assert_4_488_calls_option.get_0
Property: assert
Result: ✅ pass

Obligation: assert_4_488
Property: assert
Result: ✅ pass

Obligation: assert_5_515
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
