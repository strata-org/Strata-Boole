/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: sum_of_slice — sum of a slice of scalars modulo the group order ℓ
Source: dalek-lite `curve25519-dalek/src/scalar_helpers.rs`, `Scalar::sum_of_slice`
        (backs `impl Sum for Scalar`, used by multiscalar and batch code paths)

Spec in words:  result ≡ Σ scalars[i]  (mod ℓ),  and result is canonical (< ℓ).
ℓ = 2^252 + 27742317777372353535851937790883648493 is the order of the Ed25519 group.

Why it is not trivial: the proof needs a loop invariant relating the running
accumulator to a recursively defined prefix sum, plus the modular identity
(a mod ℓ + b) mod ℓ = (a + b) mod ℓ at every step.  dalek-lite's Verus proof
needs five lemma calls, four proof blocks and three sequence-extensionality
asserts around the loop; in Boole the invariant alone suffices — cvc5
discharges every obligation, and lean-smt replays each cvc5 proof in the Lean
kernel.

Level 1 — Verus source (verbatim):

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

  Spec functions (curve25519-dalek/src/specs/scalar_specs.rs):

  pub open spec fn sum_of_scalars(scalars: Seq<Scalar>) -> nat
      decreases scalars.len(),
  {
      if scalars.len() == 0 { 0 }
      else {
          let last = (scalars.len() - 1) as int;
          group_canonical((sum_of_scalars(scalars.subrange(0, last)) + scalar_as_nat(&scalars[last])))
      }
  }
  pub open spec fn scalar_congruent_nat(s: &Scalar, n: nat) -> bool {
      scalar_as_canonical(s) == group_canonical(n)
  }
-/

/-
Level 2 — Boole encoding

  Scalar := Map int int        the Rust `Scalar { bytes: [u8; 32] }`; `s[j]` is byte j.
  bytes_are_u8(s)              every byte is in [0, 256): the u8 typing fact Rust gives
                               for free, stated explicitly and carried through the
                               contracts and the loop invariant.  (Bytes as `bv W8`
                               are not used because lean-smt cannot replay
                               bit-vector-to-integer reasoning.)
  scalar_as_nat(s)             the Verus `u8_32_as_nat`: little-endian value of the 32 bytes.
  is_canonical_scalar(s)       the Verus definition: value < ℓ and bytes[31] <= 127.
  group_canonical(n)           n mod ℓ.
  scalars : Map int Scalar     the input slice; `scalars[i]` is the i-th scalar.
  sum_of_scalars(s, n)         the Verus spec function, recursive over the prefix length;
                               its two unfolding equations are stated as axioms because
                               int-recursive functions are exported to SMT as uninterpreted.
  scalar_zero()                `Scalar::ZERO`, left uninterpreted with its three
                               properties (value 0, canonical, u8 bytes) as axioms —
                               what dalek-lite proves in `lemma_scalar_zero_properties`.
  Scalar_add                   procedure stub carrying the Verus contract of `&Scalar + &Scalar`
                               (result ≡ a + b mod ℓ, canonical), verified separately in
                               dalek-lite; the `bytes_are_u8` clause is Rust typing, not a
                               Verus clause.
  The loop invariants are the Verus ones, with the u8 typing fact made explicit.

  Level 3: `useArrayTheory := false` lowers `Map` to an uninterpreted sort with select/update
  (lean-smt has no SMT-LIB array support). Every obligation is closed by `smt`, i.e. cvc5's
  proof is replayed and checked by the Lean kernel.
-/
private def sumOfSliceSeed : StrataDDM.Program :=
#strata
program Boole;

type Scalar := Map int int;
type Scalars := Map int Scalar;

function scalar_as_nat(s: Scalar) : int {
  s[0] + 256 * s[1] + 65536 * s[2] + 16777216 * s[3] + 4294967296 * s[4] + 1099511627776 * s[5] + 281474976710656 * s[6] + 72057594037927936 * s[7] + 18446744073709551616 * s[8] + 4722366482869645213696 * s[9] + 1208925819614629174706176 * s[10] + 309485009821345068724781056 * s[11] + 79228162514264337593543950336 * s[12] + 20282409603651670423947251286016 * s[13] + 5192296858534827628530496329220096 * s[14] + 1329227995784915872903807060280344576 * s[15] + 340282366920938463463374607431768211456 * s[16] + 87112285931760246646623899502532662132736 * s[17] + 22300745198530623141535718272648361505980416 * s[18] + 5708990770823839524233143877797980545530986496 * s[19] + 1461501637330902918203684832716283019655932542976 * s[20] + 374144419156711147060143317175368453031918731001856 * s[21] + 95780971304118053647396689196894323976171195136475136 * s[22] + 24519928653854221733733552434404946937899825954937634816 * s[23] + 6277101735386680763835789423207666416102355444464034512896 * s[24] + 1606938044258990275541962092341162602522202993782792835301376 * s[25] + 411376139330301510538742295639337626245683966408394965837152256 * s[26] + 105312291668557186697918027683670432318895095400549111254310977536 * s[27] + 26959946667150639794667015087019630673637144422540572481103610249216 * s[28] + 6901746346790563787434755862277025452451108972170386555162524223799296 * s[29] + 1766847064778384329583297500742918515827483896875618958121606201292619776 * s[30] + 452312848583266388373324160190187140051835877600158453279131187530910662656 * s[31]
}
function group_canonical(n: int) : int { n mod 7237005577332262213973186563042994240857116359379907606001950938285454250989 }
function is_canonical_scalar(s: Scalar) : bool {
  scalar_as_nat(s) < 7237005577332262213973186563042994240857116359379907606001950938285454250989 && s[31] <= 127
}
function bytes_are_u8(s: Scalar) : bool {
  ∀ j: int . 0 <= j && j < 32 ==> 0 <= s[j] && s[j] < 256
}
function scalar_zero() : Scalar;

axiom scalar_as_nat(scalar_zero()) == 0;
axiom is_canonical_scalar(scalar_zero());
axiom bytes_are_u8(scalar_zero());

rec function sum_of_scalars(s: Scalars, n: int) : int
  decreases n
{
  if n <= 0 then 0 else group_canonical(sum_of_scalars(s, n - 1) + scalar_as_nat(s[n - 1]))
}
;
axiom (∀ s: Scalars . sum_of_scalars(s, 0) == 0);
axiom (∀ s: Scalars, n: int . n > 0 ==> sum_of_scalars(s, n) == group_canonical(sum_of_scalars(s, n - 1) + scalar_as_nat(s[n - 1])));

procedure Scalar_add(a: Scalar, b: Scalar) returns (result: Scalar)
spec {
  ensures scalar_as_nat(result) == group_canonical(scalar_as_nat(a) + scalar_as_nat(b));
  ensures is_canonical_scalar(result);
  ensures bytes_are_u8(result);
}
{ assume false; };

procedure sum_of_slice(scalars: Scalars, n: int) returns (result: Scalar)
spec {
  requires n >= 0;
  requires (∀ i: int . 0 <= i && i < n ==> is_canonical_scalar(scalars[i]));
  requires (∀ i: int . 0 <= i && i < n ==> bytes_are_u8(scalars[i]));
  ensures scalar_as_nat(result) == sum_of_scalars(scalars, n);
  ensures is_canonical_scalar(result);
  ensures bytes_are_u8(result);
}
{
  var acc: Scalar;
  acc := scalar_zero();
  for i : int := 0 to (n - 1) by 1
    invariant 0 <= i && i <= n
    invariant is_canonical_scalar(acc)
    invariant bytes_are_u8(acc)
    invariant scalar_as_nat(acc) == sum_of_scalars(scalars, i)
  {
    call acc := Scalar_add(acc, scalars[i]);
  }
  result := acc;
};
#end

-- Level 3 — Lean backend (lean-smt: every cvc5 proof replayed in the Lean kernel)
/-- info:
Obligation: sum_of_scalars_terminates_0
Property: assert
Result: ✅ pass

Obligation: sum_of_scalars_terminates_1
Property: assert
Result: ✅ pass

Obligation: Scalar_add_ensures_5_8293
Property: assert
Result: ✅ pass

Obligation: Scalar_add_ensures_6_8382
Property: assert
Result: ✅ pass

Obligation: Scalar_add_ensures_7_8421
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_6_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_6_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_6_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_6_3
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_6_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_6_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_6_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_6_3
Property: assert
Result: ✅ pass

Obligation: sum_of_slice_ensures_12_8728
Property: assert
Result: ✅ pass

Obligation: sum_of_slice_ensures_13_8791
Property: assert
Result: ✅ pass

Obligation: sum_of_slice_ensures_14_8830
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" sumOfSliceSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole sumOfSliceSeed (options := { useArrayTheory := false }) := by
  gen_smt_vcs_boole
  all_goals smt
