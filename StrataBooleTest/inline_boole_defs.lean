/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
Regression test for the `inline_boole_defs` tactic.

The SMT→Lean bridge introduces each Boole `function f(..) : T { body }` into the
generated goal as a non-dependent `let` (printed as `have f := fun .. => body`).
Tactics treat the let-bound `f` as an opaque atom, so an obligation that needs the
body — here the range of a 32-byte little-endian value — is not provable directly.
`inline_boole_defs` zeta/beta-reduces the definition into the goal, after which
`omega` closes it.
-/

private def bytesSeed : StrataDDM.Program :=
#strata
program Boole;

type Bytes32 := Map int int;

function u8_32_as_nat(b: Bytes32) : int {
  b[0] + 256 * b[1] + 65536 * b[2] + 16777216 * b[3] + 4294967296 * b[4] + 1099511627776 * b[5] + 281474976710656 * b[6] + 72057594037927936 * b[7] + 18446744073709551616 * b[8] + 4722366482869645213696 * b[9] + 1208925819614629174706176 * b[10] + 309485009821345068724781056 * b[11] + 79228162514264337593543950336 * b[12] + 20282409603651670423947251286016 * b[13] + 5192296858534827628530496329220096 * b[14] + 1329227995784915872903807060280344576 * b[15] + 340282366920938463463374607431768211456 * b[16] + 87112285931760246646623899502532662132736 * b[17] + 22300745198530623141535718272648361505980416 * b[18] + 5708990770823839524233143877797980545530986496 * b[19] + 1461501637330902918203684832716283019655932542976 * b[20] + 374144419156711147060143317175368453031918731001856 * b[21] + 95780971304118053647396689196894323976171195136475136 * b[22] + 24519928653854221733733552434404946937899825954937634816 * b[23] + 6277101735386680763835789423207666416102355444464034512896 * b[24] + 1606938044258990275541962092341162602522202993782792835301376 * b[25] + 411376139330301510538742295639337626245683966408394965837152256 * b[26] + 105312291668557186697918027683670432318895095400549111254310977536 * b[27] + 26959946667150639794667015087019630673637144422540572481103610249216 * b[28] + 6901746346790563787434755862277025452451108972170386555162524223799296 * b[29] + 1766847064778384329583297500742918515827483896875618958121606201292619776 * b[30] + 452312848583266388373324160190187140051835877600158453279131187530910662656 * b[31]
}

procedure bytes_value(b: Bytes32) returns (n: int)
spec {
  requires 0 <= b[0] && b[0] < 256;
  requires 0 <= b[1] && b[1] < 256;
  requires 0 <= b[2] && b[2] < 256;
  requires 0 <= b[3] && b[3] < 256;
  requires 0 <= b[4] && b[4] < 256;
  requires 0 <= b[5] && b[5] < 256;
  requires 0 <= b[6] && b[6] < 256;
  requires 0 <= b[7] && b[7] < 256;
  requires 0 <= b[8] && b[8] < 256;
  requires 0 <= b[9] && b[9] < 256;
  requires 0 <= b[10] && b[10] < 256;
  requires 0 <= b[11] && b[11] < 256;
  requires 0 <= b[12] && b[12] < 256;
  requires 0 <= b[13] && b[13] < 256;
  requires 0 <= b[14] && b[14] < 256;
  requires 0 <= b[15] && b[15] < 256;
  requires 0 <= b[16] && b[16] < 256;
  requires 0 <= b[17] && b[17] < 256;
  requires 0 <= b[18] && b[18] < 256;
  requires 0 <= b[19] && b[19] < 256;
  requires 0 <= b[20] && b[20] < 256;
  requires 0 <= b[21] && b[21] < 256;
  requires 0 <= b[22] && b[22] < 256;
  requires 0 <= b[23] && b[23] < 256;
  requires 0 <= b[24] && b[24] < 256;
  requires 0 <= b[25] && b[25] < 256;
  requires 0 <= b[26] && b[26] < 256;
  requires 0 <= b[27] && b[27] < 256;
  requires 0 <= b[28] && b[28] < 256;
  requires 0 <= b[29] && b[29] < 256;
  requires 0 <= b[30] && b[30] < 256;
  requires 0 <= b[31] && b[31] < 256;
  ensures n == u8_32_as_nat(b);
  ensures 0 <= n && n < 115792089237316195423570985008687907853269984665640564039457584007913129639936;
}
{
  n := u8_32_as_nat(b);
};
#end

/-- info:
Obligation: bytes_value_ensures_32_3573
Property: assert
Result: ✅ pass

Obligation: bytes_value_ensures_33_3605
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bytesSeed (options := .quiet)

-- Without `inline_boole_defs` the range obligation is stuck behind the opaque
-- `have u8_32_as_nat := ...`; with it, `omega` sees the 32-term sum (the first
-- obligation reduces to `True`, hence `trivial`).
example : Strata.smtVCsCorrectBoole bytesSeed (options := { useArrayTheory := false }) := by
  gen_smt_vcs_boole
  all_goals (inline_boole_defs; intros; first | trivial | omega)
