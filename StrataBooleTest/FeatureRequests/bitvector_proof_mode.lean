/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors:
- Source: VeruSAGE-Bench Vest
  `regular__leb128__impl2__lemma_spec_parse_low_7_bits.rs`
- Verus context: LEB128 encodes integers as a sequence of bytes where bit 7
  is a continuation flag and bits [6:0] carry data. The proof of
  `lemma_spec_parse_low_7_bits` discharges two bitvector identities
    assert(take_low_7_bits!(take_low_7_bits!(s0)) == take_low_7_bits!(s0))
      by (bit_vector);
    assert(take_low_7_bits!(rest << 7 | take_low_7_bits!(s0) as UInt)
      == take_low_7_bits!(s0)) by (bit_vector);

- `bitvectorProofModeSeedRewrite`: translation of rust spec with lemma.
  The flags `recursiveFnsAsDefineFunRec`, `fmf-fun` make cvc5 unfold the definition
  The lemma passes. Under `fmf-fun` the odd `spec_parse_rec_terminates_N`
  obligations are unknown. Termination is shown by the next program.
- `bitvectorProofModeRecursionSeed`: shows `spec_parse_rec` termination.

*not neccessary? - not in original spec*
- Gap: Boole has no `by (bit_vector)` proof block. Both identities must be
  stated as explicit axioms rather than discharged automatically.
- Remaining gap: a proof-mode block that routes pure bitvector sub-goals to
  a bitvector decision procedure without explicit axioms.
-/

private def bitvectorProofModeSeedRewrite : StrataDDM.Program :=
#strata
program Boole;

function low7(b: bv W8) : bv W8{
  b & bv{8}(127)
}

function low7_64(b : bv W64) : bv W8{
  as_bv8(as_uint(b)) & bv{8}(127)
}

function is_high_8_bit(b: bv W8) : bool{
  b >= bv{8}(128)
}

rec
function spec_parse_rec(s : Sequence (bv W8)) : option (pair int (bv W64))
decreases Sequence.length(s)
{
  if Sequence.length(s) != 0 then
    if is_high_8_bit(Sequence.select(s, 0))
      then match spec_parse_rec(Sequence.dropFirst(s)) {
        some((n: int, v2: bv W64)) =>
          if n < 18446744073709551615            // usize::MAX (64 bit)
            && bv{64}(0) < v2
            && v2 <= as_bv64(144115188075855871) // n_bit_max_unsigned!(8 * uint_size!() - 7)
              then some((n + 1, (v2 << bv{64}(7)) | as_bv64(as_uint(low7(Sequence.select(s, 0))))))
              else none<pair int (bv W64)>,
        none => none<pair int (bv W64)>
      }
    else some((1, as_bv64(as_uint(low7(Sequence.select(s, 0))))))
  else none<pair int (bv W64)>
};

procedure leb128_low7_seed(s: Sequence (bv W8)) returns ()
spec {
  requires Sequence.length(s) != 0;
  ensures [ensures_bv]: spec_parse_rec(s) matches some((_, x : bv W64)) ==>
    let s0 : bv W8 := Sequence.select(s, 0) in
    low7_64(x) == low7(s0);
}
{};

#end
/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_3
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_4
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_5
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_6
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_7
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_8
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_9
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_10
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_11
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.select_12
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.select_13
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_terminates_0
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_1
Property: assert
Result: ❓ unknown

Obligation: spec_parse_rec_terminates_2
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_3
Property: assert
Result: ❓ unknown

Obligation: spec_parse_rec_terminates_4
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_5
Property: assert
Result: ❓ unknown

Obligation: spec_parse_rec_terminates_6
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_7
Property: assert
Result: ❓ unknown

Obligation: spec_parse_rec_terminates_8
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_9
Property: assert
Result: ❓ unknown

Obligation: spec_parse_rec_terminates_10
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_11
Property: assert
Result: ❓ unknown

Obligation: leb128_low7_seed_post_ensures_bv_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: leb128_low7_seed_post_ensures_bv_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: ensures_bv
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorProofModeSeedRewrite
  (options := { Core.VerifyOptions.quiet with
                 recursiveFnsAsDefineFunRec := true,
                 solverOptions := #[("fmf-fun", "true")],
                 solverTimeout := 60 })



private def bitvectorProofModeRecursionSeed : StrataDDM.Program :=
#strata
program Boole;

function low7(b: bv W8) : bv W8{
  b & bv{8}(127)
}

function low7_64(b : bv W64) : bv W8{
  as_bv8(as_uint(b)) & bv{8}(127)
}

function is_high_8_bit(b: bv W8) : bool{
  b >= bv{8}(128)
}

rec
function spec_parse_rec(s : Sequence (bv W8)) : option (pair int (bv W64))
decreases Sequence.length(s)
{
  if Sequence.length(s) != 0 then
    if is_high_8_bit(Sequence.select(s, 0))
      then match spec_parse_rec(Sequence.dropFirst(s)) {
        some((n: int, v2: bv W64)) =>
          if n < 18446744073709551615 && bv{64}(0) < v2 && v2 <= as_bv64(144115188075855871)
            then some((n + 1, (v2 << bv{64}(7)) | as_bv64(as_uint(low7(Sequence.select(s, 0))))))
            else none<pair int (bv W64)>,
        none => none<pair int (bv W64)>
      }
    else some((1, as_bv64(as_uint(low7(Sequence.select(s, 0))))))
  else none<pair int (bv W64)>
};

#end
/--
info:
Obligation: option.get_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: option.getOrElse_body_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_3
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_4
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_5
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_6
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_7
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_8
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_9
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.drop_10
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_option..val_11
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.select_12
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_body_calls_Sequence.select_13
Property: out-of-bounds access check
Result: ✅ pass

Obligation: spec_parse_rec_terminates_0
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_1
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_2
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_3
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_4
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_5
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_6
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_7
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_8
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_9
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_10
Property: assert
Result: ✅ pass

Obligation: spec_parse_rec_terminates_11
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorProofModeRecursionSeed  (options := .quiet)
