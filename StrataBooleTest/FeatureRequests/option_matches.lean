/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors:
- Source: VeruSAGE-Bench Vest
  `properties__SecureSpecCombinator__corollary_parse_surjective.rs`
  `regular__leb128__impl2__lemma_spec_parse_low_7_bits.rs`
- Verus features:
  (P) `Option<(int, T)>` as spec function return type:
      `spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>`
  (Q) `matches` destructuring in `ensures` and `exists` clauses:
      `ensures self.spec_parse(s) matches Some((_, x)) ==> low7(x) == low7(s[0])`
      `ensures exists|b| self.spec_parse(b) matches Some((_, v_)) && v_ == v`
  (R) `#[verifier::external_body]` on `theorem_serialize_parse_roundtrip`:
      the roundtrip lemma is trusted; `corollary_parse_surjective` calls it.

TODO:
  - Lean verification condition generation path for parameterized option/pair
-/

private def optionMatchesSeed : StrataDDM.Program :=
#strata
program Boole;

type Value;

function spec_parse(v: Sequence (bv W8)) : option (pair int Value);
function spec_serialize(v: Value) : Sequence (bv W8);

// --trusted roundtrip (#[verifier::external_body] equivalent)
procedure theorem_serialize_parse_roundtrip (v: Value) returns()
spec{
  free ensures spec_parse(spec_serialize(v)) matches some((n : int, v': Value))
    && (n == Sequence.length(spec_serialize(v)) &&  v' == v);
};


//corollary_parse_surjective
procedure parse_surjective_seed(v: Value) returns ()
spec {
  ensures ∃ b: Sequence (bv W8) .
    (spec_parse(b) matches some((_ , v_ : Value)) && v_ == v);
}
{
  call theorem_serialize_parse_roundtrip(v);
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

Obligation: theorem_serialize_parse_roundtrip_post_theorem_serialize_parse_roundtrip_ensures_0_1277_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: theorem_serialize_parse_roundtrip_post_theorem_serialize_parse_roundtrip_ensures_0_1277_calls_option..val_1
Property: assert
Result: ✅ pass

Obligation: parse_surjective_seed_post_parse_surjective_seed_ensures_1_1513_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assume_$__callElimAssume_theorem_serialize_parse_roundtrip_ensures_0_1277_1_calls_option..val_0
Property: assert
Result: ✅ pass

Obligation: assume_$__callElimAssume_theorem_serialize_parse_roundtrip_ensures_0_1277_1_calls_option..val_1
Property: assert
Result: ✅ pass

Obligation: parse_surjective_seed_ensures_1_1513
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" optionMatchesSeed (options := .quiet)
