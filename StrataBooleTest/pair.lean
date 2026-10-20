import StrataBoole.MetaVerifier

open Strata

private def testOptionAndTuples : StrataDDM.Program :=

#strata

program Boole;


var t : Pair int bool;

procedure test_pair_access () returns ()
{
  var t2 : Pair int bool := (1, true);
  assert isPair(t2);
  assert fst(t2) == 1;
  assert snd(t2) == true;
};

procedure p(a : int, b : int) {
  assert fst((a, b)) == a;
  assert snd((a, b)) == b;
};


var o : option (Pair int int);

procedure test_option () returns (){
  var o_none : option int := none<int>;
  var o_some : option int := some(1);
  var o2 : option (Pair bool int) := some((true, 12));

  assert get(o_some) == 1;
  assert getOrElse(o_none, 1) == get(o_some);
  assert isSome(o_some) == true;
  assert isNone(o_none) == true;
  assert isSome(o_none) == false;
  assert isNone(o_some) == false;
};

procedure negative_option(r : option int) { var x : int := get(r); };

#end

/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assert_0_236
Property: assert
Result: ✅ pass

Obligation: assert_1_257
Property: assert
Result: ✅ pass

Obligation: assert_2_280
Property: assert
Result: ✅ pass

Obligation: assert_3_342
Property: assert
Result: ✅ pass

Obligation: assert_4_369
Property: assert
Result: ✅ pass

Obligation: assert_assert_5_604_calls_option.get_0
Property: assert
Result: ✅ pass

Obligation: assert_5_604
Property: assert
Result: ✅ pass

Obligation: assert_assert_6_631_calls_option.get_0
Property: assert
Result: ✅ pass

Obligation: assert_6_631
Property: assert
Result: ✅ pass

Obligation: assert_7_677
Property: assert
Result: ✅ pass

Obligation: assert_8_710
Property: assert
Result: ✅ pass

Obligation: assert_9_743
Property: assert
Result: ✅ pass

Obligation: assert_10_777
Property: assert
Result: ✅ pass

Obligation: init_calls_option.get_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" testOptionAndTuples (options := .quiet)


/-
example : Strata.smtVCsCorrectBoole testOptionAndTuples := by
  gen_smt_vcs_boole
  all_goals (try grind)
-/
