/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: zeroize — cryptographic secret erasure
Source: dalek-lite `curve25519-dalek/src/scalar.rs`, lines 1303–1315

Security relevance:
  Private key material lives in a Scalar's 32-byte array.  After use, every
  byte must be overwritten.  Without a formal guarantee the compiler could
  elide the writes as "dead stores".  This postcondition rules that out:
  every byte is 0 after zeroize returns.

Level 1 — Verus source (verbatim):

  fn zeroize(&mut self)
      ensures
          forall|i: int| 0 <= i < 32 ==> #[trigger] self.bytes[i] == 0u8,
  {
      crate::core_assumes::zeroize_bytes32(&mut self.bytes);
  }
-/

-- Level 2 — Boole encoding
-- `is_zeroed` abstracts `∀ i ∈ [0,32). bytes[i] == 0`; `select_byte` is the
-- byte-indexing projection. Two axioms: (1) zeroize_fn always produces a zeroed
-- scalar; (2) zeroed ==> every selected byte is 0. Implication in Boole is `==>`.
private def zeroizeSeed : StrataDDM.Program :=
#strata
program Boole;

type Scalar;

function zeroize_fn(s: Scalar) : Scalar;
function select_byte(s: Scalar, i: int) : int;
function is_zeroed(s: Scalar) : bool;

axiom (∀ s: Scalar . is_zeroed(zeroize_fn(s)));
axiom (∀ s: Scalar . ∀ i: int . is_zeroed(s) ==> select_byte(s, i) == 0);

procedure zeroize(s: Scalar) returns (result: Scalar)
spec {
  ensures is_zeroed(result);
  ensures (∀ i: int . select_byte(result, i) == 0);
}
{
  result := zeroize_fn(s);
};
#end

-- Level 3 — Lean backend
#eval Strata.Boole.verify "cvc5" zeroizeSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole zeroizeSeed := by
  gen_smt_vcs_boole
  all_goals (try smt)
  all_goals decide
