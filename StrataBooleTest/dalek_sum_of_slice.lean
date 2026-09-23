/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: sum_of_slice — translated by verus-lean from the Verus export of dalek-lite.

GENERATED FILE.  Produced by `verus-boogie/dalek/rust_to_boole.sh sum_of_slice`:
  1. the Verus fork exports the VLIR of the crate modules the function reaches;
  2. `verus-lean boole --only sum_of_slice --u8-as-int --drop-proof-hints
     --values-invariants --literal-consts-as-axioms --index-by-prefix --total-select --short-names`
     turns them into the Boole program below (callees as contract stubs, u8 and nat
     as int with their typing facts, no Verus proof hints, the recursive spec fn
     indexed by prefix length);
  3. this wrapper adds the Verus source and the two verification levels.
The hand-written counterpart is dalek_sum_of_slice.lean.

Verus source (verbatim from the input Rust module):

  /// Compute the sum of all scalars in a slice.
  ///
  /// # Returns
  ///
  /// The sum of all scalars modulo the group order.
  ///
  /// # Example
  ///
  /// ```
  /// # use curve25519_dalek::scalar::Scalar;
  /// let scalars = [
  ///     Scalar::from(2u64),
  ///     Scalar::from(3u64),
  ///     Scalar::from(5u64),
  /// ];
  ///
  /// let sum = Scalar::sum_of_slice(&scalars);
  /// assert_eq!(sum, Scalar::from(10u64));
  /// ```
  #[allow(clippy::needless_range_loop, clippy::op_ref)]
  pub fn sum_of_slice(scalars: &[Scalar]) -> (result: Scalar)
      requires
          forall|i: int| #![auto] 0 <= i < scalars@.len() ==> is_canonical_scalar(&scalars@[i]),
      ensures
          scalar_as_nat(&result) < group_order(),
          is_canonical_scalar(&result),
          scalar_congruent_nat(&result, sum_of_scalars(scalars@)),
  {
      let n = scalars.len();
      let mut acc = Scalar::ZERO;

      proof {
          lemma_scalar_zero_properties();
          assert(scalars@.subrange(0, 0) =~= Seq::<Scalar>::empty());
      }

      for i in 0..n
          invariant
              n == scalars.len(),
              forall|j: int|
                  #![auto]
                  0 <= j < scalars@.len() ==> is_canonical_scalar(&scalars@[j]),
              scalar_as_nat(&acc) < group_order(),
              is_canonical_scalar(&acc),
              scalar_congruent_nat(&acc, sum_of_scalars(scalars@.subrange(0, i as int))),
      {
          let _old_acc = acc;

          proof {
              // Inline: sum extends by one element
              let sub = scalars@.subrange(0, (i + 1) as int);
              assert(sub.subrange(0, i as int) =~= scalars@.subrange(0, i as int));
          }

          acc = &acc + &scalars[i];

          proof {
              let L = group_order();
              let acc_val = u8_32_as_nat(&acc.bytes);
              let old_acc_val = u8_32_as_nat(&_old_acc.bytes);
              let scalar_val = u8_32_as_nat(&scalars[i as int].bytes);
              let sum_prev = sum_of_scalars(scalars@.subrange(0, i as int));

              lemma_mod_bound(old_acc_val as int + scalar_val as int, L as int);
              lemma_add_mod_noop(old_acc_val as int, scalar_val as int, L as int);
              lemma_add_mod_noop(sum_prev as int, scalar_val as int, L as int);
              lemma_mod_twice(sum_prev as int + scalar_val as int, L as int);
          }
      }

      proof {
          assert(scalars@.subrange(0, n as int) =~= scalars@);
      }

      acc
  }
-/

/-
Boole program, exactly as emitted by the translator.
-/
private def sumofsliceTranslatedSeed : StrataDDM.Program :=
#strata
program Boole;
type Scalar := Sequence int;
function Scalar_wf (s : Scalar) : bool;
axiom [Scalar_wf_def]: ∀ s : Scalar :: Scalar_wf(s) == (Sequence.length(s) == 32 && ∀ k : int :: 0 <= k && k < 32 ==> 0 <= Sequence.select!(s, k) && Sequence.select!(s, k) < 256);
function u8_32_as_nat (bytes : Sequence int) : nat {
  nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_add(nat_mul(nat_fromInt(Sequence.select!(bytes, 0)), nat_fromInt(1)), nat_mul(nat_fromInt(Sequence.select!(bytes, 1)), nat_fromInt(256))), nat_mul(nat_fromInt(Sequence.select!(bytes, 2)), nat_fromInt(65536))), nat_mul(nat_fromInt(Sequence.select!(bytes, 3)), nat_fromInt(16777216))), nat_mul(nat_fromInt(Sequence.select!(bytes, 4)), nat_fromInt(4294967296))), nat_mul(nat_fromInt(Sequence.select!(bytes, 5)), nat_fromInt(1099511627776))), nat_mul(nat_fromInt(Sequence.select!(bytes, 6)), nat_fromInt(281474976710656))), nat_mul(nat_fromInt(Sequence.select!(bytes, 7)), nat_fromInt(72057594037927936))), nat_mul(nat_fromInt(Sequence.select!(bytes, 8)), nat_fromInt(18446744073709551616))), nat_mul(nat_fromInt(Sequence.select!(bytes, 9)), nat_fromInt(4722366482869645213696))), nat_mul(nat_fromInt(Sequence.select!(bytes, 10)), nat_fromInt(1208925819614629174706176))), nat_mul(nat_fromInt(Sequence.select!(bytes, 11)), nat_fromInt(309485009821345068724781056))), nat_mul(nat_fromInt(Sequence.select!(bytes, 12)), nat_fromInt(79228162514264337593543950336))), nat_mul(nat_fromInt(Sequence.select!(bytes, 13)), nat_fromInt(20282409603651670423947251286016))), nat_mul(nat_fromInt(Sequence.select!(bytes, 14)), nat_fromInt(5192296858534827628530496329220096))), nat_mul(nat_fromInt(Sequence.select!(bytes, 15)), nat_fromInt(1329227995784915872903807060280344576))), nat_mul(nat_fromInt(Sequence.select!(bytes, 16)), nat_fromInt(340282366920938463463374607431768211456))), nat_mul(nat_fromInt(Sequence.select!(bytes, 17)), nat_fromInt(87112285931760246646623899502532662132736))), nat_mul(nat_fromInt(Sequence.select!(bytes, 18)), nat_fromInt(22300745198530623141535718272648361505980416))), nat_mul(nat_fromInt(Sequence.select!(bytes, 19)), nat_fromInt(5708990770823839524233143877797980545530986496))), nat_mul(nat_fromInt(Sequence.select!(bytes, 20)), nat_fromInt(1461501637330902918203684832716283019655932542976))), nat_mul(nat_fromInt(Sequence.select!(bytes, 21)), nat_fromInt(374144419156711147060143317175368453031918731001856))), nat_mul(nat_fromInt(Sequence.select!(bytes, 22)), nat_fromInt(95780971304118053647396689196894323976171195136475136))), nat_mul(nat_fromInt(Sequence.select!(bytes, 23)), nat_fromInt(24519928653854221733733552434404946937899825954937634816))), nat_mul(nat_fromInt(Sequence.select!(bytes, 24)), nat_fromInt(6277101735386680763835789423207666416102355444464034512896))), nat_mul(nat_fromInt(Sequence.select!(bytes, 25)), nat_fromInt(1606938044258990275541962092341162602522202993782792835301376))), nat_mul(nat_fromInt(Sequence.select!(bytes, 26)), nat_fromInt(411376139330301510538742295639337626245683966408394965837152256))), nat_mul(nat_fromInt(Sequence.select!(bytes, 27)), nat_fromInt(105312291668557186697918027683670432318895095400549111254310977536))), nat_mul(nat_fromInt(Sequence.select!(bytes, 28)), nat_fromInt(26959946667150639794667015087019630673637144422540572481103610249216))), nat_mul(nat_fromInt(Sequence.select!(bytes, 29)), nat_fromInt(6901746346790563787434755862277025452451108972170386555162524223799296))), nat_mul(nat_fromInt(Sequence.select!(bytes, 30)), nat_fromInt(1766847064778384329583297500742918515827483896875618958121606201292619776))), nat_mul(nat_fromInt(Sequence.select!(bytes, 31)), nat_fromInt(452312848583266388373324160190187140051835877600158453279131187530910662656)))
}
function group_order () : nat {
  nat_fromInt(7237005577332262213973186563042994240857116359379907606001950938285454250989)
}
function is_canonical_scalar (s : Scalar) : bool {
  nat_lt(u8_32_as_nat(s), group_order) && Sequence.select!(s, 31) <= 127
}
function scalar_as_nat (s : Scalar) : nat {
  u8_32_as_nat(s)
}
function group_canonical (n : nat) : nat {
  nat_mod(n, group_order)
}
function u8_32_as_group_canonical (bytes : Sequence int) : nat {
  group_canonical(u8_32_as_nat(bytes))
}
function scalar_as_canonical (s : Scalar) : nat {
  u8_32_as_group_canonical(s)
}
rec function sum_of_scalars (scalars : Sequence Scalar, n : nat) : nat
  requires nat_toInt(n) <= Sequence.length(scalars);
  decreases nat_toInt(n)
{
  if nat_toInt(n) == 0 then nat_fromInt(0) else group_canonical(nat_add(sum_of_scalars(scalars, nat_fromInt(nat_toInt(n) - 1)), scalar_as_nat(Sequence.select(scalars, nat_toInt(n) - 1))))
};
axiom [sum_of_scalars_unfold]: ∀ scalars : (Sequence Scalar), n : nat :: nat_toInt(n) <= Sequence.length(scalars) ==> sum_of_scalars(scalars, n) == (if nat_toInt(n) == 0 then nat_fromInt(0) else group_canonical(nat_add(sum_of_scalars(scalars, nat_fromInt(nat_toInt(n) - 1)), scalar_as_nat(Sequence.select(scalars, nat_toInt(n) - 1)))));
function scalar_congruent_nat (s : Scalar, n : nat) : bool {
  nat_toInt(scalar_as_canonical(s)) == nat_toInt(group_canonical(n))
}
function Scalar_obeys_add_spec () : bool {
  false
}
function Scalar_add_req (self : Scalar, rhs : Scalar) : bool {
  is_canonical_scalar(self) && is_canonical_scalar(rhs)
}
function Scalar_add_spec (self : Scalar, rhs : Scalar) : Scalar;
function Scalar_ZERO () : Scalar;
axiom [Scalar_ZERO_lit_0]: Sequence.length(Scalar_ZERO) == 32;
axiom [Scalar_ZERO_lit_1]: ∀ k : int :: 0 <= k && k < 32 ==> Sequence.select!(Scalar_ZERO, k) == 0;
axiom [lemma_scalar_zero_properties_ensures_0]: nat_toInt(scalar_as_nat(Scalar_ZERO)) == 0;
axiom [lemma_scalar_zero_properties_ensures_1]: nat_lt(scalar_as_nat(Scalar_ZERO), group_order);
axiom [lemma_scalar_zero_properties_ensures_2]: is_canonical_scalar(Scalar_ZERO);
axiom [lemma_scalar_zero_properties_ensures_3]: scalar_congruent_nat(Scalar_ZERO, nat_fromInt(0));
procedure Scalar_add (self : Scalar, _rhs : Scalar) returns (result : Scalar)
spec {
  requires Scalar_wf(self);
  requires Scalar_wf(_rhs);
  ensures Scalar_wf(result);
  requires Scalar_add_req(self, _rhs);
  ensures Scalar_obeys_add_spec ==> result == Scalar_add_spec(self, _rhs);
  ensures nat_toInt(scalar_as_nat(result)) == nat_toInt(group_canonical(nat_add(scalar_as_nat(self), scalar_as_nat(_rhs))));
  ensures is_canonical_scalar(result);
}
{
  assume false;
};
procedure sum_of_slice (scalars : Sequence Scalar) returns (result : Scalar)
spec {
  requires ∀ i_elem : int :: 0 <= i_elem && i_elem < Sequence.length(scalars) ==> Scalar_wf(Sequence.select(scalars, i_elem));
  ensures Scalar_wf(result);
  requires ∀ i : int :: 0 <= i && i < Sequence.length(scalars) ==> is_canonical_scalar(Sequence.select(scalars, i));
  ensures nat_lt(scalar_as_nat(result), group_order);
  ensures is_canonical_scalar(result);
  ensures scalar_congruent_nat(result, sum_of_scalars(scalars, nat_fromInt(Sequence.length(scalars))));
}
{
  var n : int;
  var acc : Scalar;
  assume Sequence.length(scalars) <= 18446744073709551615;
  n := Sequence.length(scalars);
  acc := Scalar_ZERO;
  for i : int := 0 to Sequence.length(scalars) - 1
    invariant 0 <= i && i <= Sequence.length(scalars)
    invariant Scalar_wf(acc)
    invariant n == Sequence.length(scalars)
    invariant ∀ j : int :: 0 <= j && j < Sequence.length(scalars) ==> is_canonical_scalar(Sequence.select(scalars, j))
    invariant nat_lt(scalar_as_nat(acc), group_order)
    invariant is_canonical_scalar(acc)
    invariant nat_toInt(scalar_as_nat(acc)) == nat_toInt(sum_of_scalars(scalars, nat_fromInt(i)))
  {
    call acc := Scalar_add(acc, Sequence.select(scalars, i));
  }
  result := acc;
  exit sum_of_slice;
};
#end

/-- info:
Obligation: pos.toInt_body_calls_pos..xO_h_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_body_calls_pos..xI_h_1
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_2
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_3
Property: assert
Result: ✅ pass

Obligation: sum_of_scalars_body_calls_sum_of_scalars_0
Property: assert
Result: ✅ pass

Obligation: sum_of_scalars_body_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: sum_of_scalars_terminates_0
Property: assert
Result: ✅ pass

Obligation: sum_of_scalars_terminates_1
Property: assert
Result: ✅ pass

Obligation: Scalar_add_ensures_3_9847
Property: assert
Result: ✅ pass

Obligation: Scalar_add_ensures_5_9915
Property: assert
Result: ✅ pass

Obligation: Scalar_add_ensures_6_9990
Property: assert
Result: ✅ pass

Obligation: Scalar_add_ensures_7_10115
Property: assert
Result: ✅ pass

Obligation: sum_of_slice_pre_sum_of_slice_requires_9_10261_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: sum_of_slice_pre_sum_of_slice_requires_11_10419_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: sum_of_slice_post_sum_of_slice_ensures_14_10631_calls_sum_of_scalars_0
Property: assert
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_sum_of_scalars_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_10_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_10_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_10_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_10_3
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_10_4
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_10_5
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_10_6
Property: assert
Result: ✅ pass

Obligation: init_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_Scalar_add_requires_1_9791_3
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Scalar_add_requires_2_9819_4
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Scalar_add_requires_4_9876_5
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_10_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_10_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_10_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_10_3
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_10_4
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_10_5
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_10_6
Property: assert
Result: ✅ pass

Obligation: sum_of_slice_ensures_10_10390
Property: assert
Result: ✅ pass

Obligation: sum_of_slice_ensures_12_10538
Property: assert
Result: ✅ pass

Obligation: sum_of_slice_ensures_13_10592
Property: assert
Result: ✅ pass

Obligation: sum_of_slice_ensures_14_10631
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" sumofsliceTranslatedSeed (options := .quiet)

-- Lean kernel: every obligation is discharged by a tactic whose proof the Lean
-- kernel checks, over the native `nat`/`pos` datatypes (Strata translates them
-- to Lean inductives, `Strata.SMT.DT.*`).
--
-- The three goals about `pos` itself state facts of the inductive - the three
-- constructors are exhaustive, and a selector's result ranks below its
-- constructor.  Case analysis settles them; a solver cannot, since to it the
-- testers and selectors are opaque functions.  Everything else goes to cvc5
-- with its proof replayed in the kernel (`smt`), to `grind`, or, where the goal
-- needs a Boole `function` body rather than its name, to `inline_boole_defs`
-- (the analogue of Verus's `reveal`) followed by `smt`.
set_option maxHeartbeats 2000000 in
example : Strata.smtVCsCorrectBoole sumofsliceTranslatedSeed := by
  gen_smt_vcs_boole
  case «pos.toInt_body_calls_pos..xI_h_1» =>
    intro p _ _
    cases p <;>
      simp_all [Strata.SMT.DT.pos.is_xH, Strata.SMT.DT.pos.is_xO, Strata.SMT.DT.pos.is_xI]
  case pos.toInt_terminates_0 =>
    intro p _ _ _ _ _ _
    cases p <;>
      simp_all [Strata.SMT.DT.pos.is_xH, Strata.SMT.DT.pos.is_xO, Strata.SMT.DT.pos.xO_h]
  case pos.toInt_terminates_1 =>
    intro p _ _ _ _ _ _
    cases p <;>
      simp_all [Strata.SMT.DT.pos.is_xH, Strata.SMT.DT.pos.is_xO, Strata.SMT.DT.pos.xI_h]
  -- `grind` first: it needs no solver and closes most of these goals in a
  -- second or two.  It is capped, because on a goal it cannot close it searches
  -- far longer than the passes below need to succeed.  cvc5 is capped for the
  -- same reason: on three of these goals its search does not terminate, and
  -- `grind` or the `inline_boole_defs` pass has those anyway.
  all_goals (try (set_option maxHeartbeats 40000 in grind))
  all_goals (try smt (timeout := .some 30))
  all_goals (inline_boole_defs; smt (timeout := .some 60))
