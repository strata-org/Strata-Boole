/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: bot_half / top_half — nibble extraction from u8
Source: dalek-lite `curve25519-dalek/src/scalar.rs`, lines 2150–2189

These are used in `as_radix_16`, which decomposes a scalar into 64 signed nibbles
for the wNAF-style fixed-base scalar multiplication in Ed25519 signing.

Level 1 — Verus source (verbatim):

  #[inline(always)]
  fn bot_half(x: u8) -> (result: u8)
      ensures
          result == x % 16,
          result <= 15,
  {
      let result = (x >> 0) & 15;
      proof { assert((x >> 0) & 15 == x % 16) by (bit_vector); }
      result
  }

  #[inline(always)]
  fn top_half(x: u8) -> (result: u8)
      ensures
          result == x / 16,
          result <= 15,
  {
      let result = (x >> 4) & 15;
      proof { assert((x >> 4) & 15 == x / 16) by (bit_vector); }
      result
  }
-/

-- Level 2 — Boole encoding
-- `x % 16 = x & 0xF` and `x / 16 = x >> 4` in unsigned 8-bit arithmetic.
-- `result <= 15` ↔ upper nibble is zero: `result & 0xF0 == 0`.
private def nibbleSeed : StrataDDM.Program :=
#strata
program Boole;

procedure bot_half(x: bv W8) returns (r: bv W8)
spec {
  ensures r == x & bv{8}(0xF);
  ensures r & bv{8}(0xF0) == bv{8}(0);
}
{ r := x & bv{8}(0xF); };

procedure top_half(x: bv W8) returns (r: bv W8)
spec {
  ensures r == x >> bv{8}(4);
  ensures r & bv{8}(0xF0) == bv{8}(0);
}
{ r := x >> bv{8}(4); };
#end

-- Level 3 — Lean backend
#eval Strata.Boole.verify "cvc5" nibbleSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole nibbleSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
  all_goals decide
