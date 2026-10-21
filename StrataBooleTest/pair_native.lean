import StrataBoole.MetaVerifier

open Strata

private def testOptionAndTuples : StrataDDM.Program :=

#strata

program Boole;


var t : pair int bool;

procedure test_pair_access () returns ()
{
  var t2 : pair int bool := (1, true);
  assert isPair(t2);
  assert fst(t2) == 1;
  assert snd(t2) == true;
};

procedure p(a : int, b : int) {
  assert fst((a, b)) == a;
  assert snd((a, b)) == b;
};

#end
/--
info:
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
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" testOptionAndTuples (options := .quiet)


/- example : Strata.smtVCsCorrectBoole testOptionAndTuples := by
  gen_smt_vcs_boole
  all_goals (try grind)
 -/
