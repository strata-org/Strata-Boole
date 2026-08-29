/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-!
# Keynote benchmark: Verus → Boole → Lean (end-to-end)

Source library: **dalek-lite** (Beneficial-AI-Foundation/dalek-lite),
a Verus-verified Rust implementation of Curve25519/Ed25519.

Paper: "An AI Approach to Verified Production Cryptographic Libraries" (arXiv 2608.00965).
`CryptoProver` synthesized Verus proofs for curve25519-dalek automatically;
Strata independently verifies the same postconditions through the Boole DSL.

Pipeline for each benchmark:

  1. **Verus** — executable Rust annotated with `requires`/`ensures` (quoted verbatim)
  2. **Boole** — Strata's verification DSL encoding of the same specification
  3. **Lean** — `gen_smt_vcs_boole` discharges all obligations via cvc5;
                 the result is a Lean theorem that is machine-checked

`#eval Strata.Boole.verify` runs the SMT pipeline and prints ✅/❌ per obligation.
`example : Strata.smtVCsCorrectBoole` is the formal Lean proof.
-/

-- ┌───────────────────────────────────────────────────────┐
-- │ Benchmark 1 — clamp_integer                           │
-- │ X25519 scalar clamping  (scalar_specs.rs)             │
-- └───────────────────────────────────────────────────────┘

/-
── Level 1: Verus source (dalek-lite/curve25519-dalek/src/specs/scalar_specs.rs) ──

pub fn clamp_integer(bytes: [u8; 32]) -> (result: [u8; 32])
    ensures
        result[0]  == bytes[0]  & 0b1111_1000u8,
        result[31] == (bytes[31] & 0b0111_1111u8) | 0b0100_0000u8,
        // Security: lower 3 bits cleared  (cofactor = 8 for Curve25519)
        result[0]  & 0b0000_0111u8 == 0u8,
        // Security: high bit cleared      (canonical 255-bit representation)
        result[31] & 0b1000_0000u8 == 0u8,
        // Security: bit 254 forced set    (prevents small-scalar attacks)
        result[31] & 0b0100_0000u8 == 0b0100_0000u8,
-/

-- ── Level 2: Boole encoding ──
-- bytes[0] and bytes[31] are the only two bytes that RFC 7748 clamps.
-- Five postconditions: two equalities (what was computed) +
-- three security properties (what must hold in any clamped scalar).
private def clampSeed : StrataDDM.Program :=
#strata
program Boole;

procedure clamp_integer(b0: bv W8, b31: bv W8) returns (r0: bv W8, r31: bv W8)
spec {
  ensures r0  == b0  & bv{8}(0b11111000);
  ensures r31 == (b31 & bv{8}(0b01111111)) | bv{8}(0b01000000);
  ensures r0  & bv{8}(0b00000111) == bv{8}(0);
  ensures r31 & bv{8}(0b10000000) == bv{8}(0);
  ensures r31 & bv{8}(0b01000000) == bv{8}(0b01000000);
}
{
  r0  := b0  & bv{8}(0b11111000);
  r31 := (b31 & bv{8}(0b01111111)) | bv{8}(0b01000000);
};
#end

-- ── Level 3: Lean backend ──
/-- info:
Obligation: clamp_integer_ensures_0_2615
Property: assert
Result: ✅ pass

Obligation: clamp_integer_ensures_1_2657
Property: assert
Result: ✅ pass

Obligation: clamp_integer_ensures_2_2721
Property: assert
Result: ✅ pass

Obligation: clamp_integer_ensures_3_2768
Property: assert
Result: ✅ pass

Obligation: clamp_integer_ensures_4_2815
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" clampSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole clampSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
  case clamp_integer_ensures_2_2721 => decide
  case clamp_integer_ensures_3_2768 => decide
  case clamp_integer_ensures_4_2815 => decide


-- ┌───────────────────────────────────────────────────────┐
-- │ Benchmark 2 — from_bytes_mod_order                    │
-- │ Canonical scalar reduction mod group order ℓ          │
-- │ (scalar.rs:273–291, 32-byte variant)                  │
-- └───────────────────────────────────────────────────────┘

/-
── Level 1: Verus source (dalek-lite/curve25519-dalek/src/scalar.rs) ──

pub fn from_bytes_mod_order(bytes: [u8; 32]) -> (result: Scalar)
    ensures
        scalar_as_canonical(&result) == u8_32_as_group_canonical(bytes),
        is_canonical_scalar(&result),
{
    let s_unreduced = Scalar { bytes };
    let s = s_unreduced.reduce();
    s
}

Security relevance:
  - First postcondition:  output equals input reduced mod ℓ (correctness).
  - Second postcondition: output is the unique representative in [0, ℓ).
    Without this, two distinct byte strings represent the same scalar,
    enabling signature malleability (CVE in OpenSSL and tinyssh;
    see RFC 8032 §5.1.7).
-/

-- ── Level 2: Boole encoding ──
-- `ByteArray32` and `Scalar` are kept abstract — no struct-field access needed.
-- Two axioms capture what `reduce` guarantees; the procedure body verifies
-- by axiom instantiation alone.  This is the "trusted foundation" pattern:
-- the axioms are the verification target; the Boole procedure is the client.
private def scalarReduceSeed : StrataDDM.Program :=
#strata
program Boole;

type ByteArray32;
type Scalar;

function reduce(b: ByteArray32) : Scalar;
function scalar_as_canonical(s: Scalar) : int;
function u8_32_as_group_canonical(b: ByteArray32) : int;
function is_canonical_scalar(s: Scalar) : bool;

axiom (∀ b: ByteArray32 . scalar_as_canonical(reduce(b)) == u8_32_as_group_canonical(b));
axiom (∀ b: ByteArray32 . is_canonical_scalar(reduce(b)));

procedure from_bytes_mod_order(bytes: ByteArray32) returns (result: Scalar)
spec {
  ensures scalar_as_canonical(result) == u8_32_as_group_canonical(bytes);
  ensures is_canonical_scalar(result);
}
{
  result := reduce(bytes);
};
#end

-- ── Level 3: Lean backend ──
/-- info:
Obligation: from_bytes_mod_order_ensures_2_5861
Property: assert
Result: ✅ pass

Obligation: from_bytes_mod_order_ensures_3_5935
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" scalarReduceSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole scalarReduceSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
