# Native `nat` in the Rust → Boole → cvc5 → Lean pipeline

> **About this branch.** `keynote-integration` is an integration branch, not a PR:
> it combines the Strata-Boole changes below with three Strata PRs that are still
> open, so it does not build on its own. `lakefile.toml` points `Strata` at a local
> path and `smt` at a private fork carrying one backported fix. The work is being
> landed as the separate PRs listed here; this branch exists to show the result
> end to end.

## Goal

Verify dalek-lite's `Scalar::sum_of_slice` end to end, fully generated:

1. **Rust** with Verus specs.
2. **Boole + cvc5** — translated to Boole, every proof obligation discharged by the solver.
3. **Lean kernel** — every obligation replayed inside Lean (lean-smt), so the solver is not trusted.

Verus's `nat` used to be translated as `int` (a flag, `--nat-as-int`). That loses the
type and needs an extra "≥ 0" fact for every nat-valued parameter, result and spec
function. The work below puts Boole's own `nat` through the whole pipeline instead —
a binary datatype, `pos = xH | xO pos | xI pos` and `nat = N0 | Npos pos`, with a
`toInt`/`fromInt` bridge only where a spec genuinely crosses into `int` (sequence
indices, the loop counter, literals).

## What was in the way

| Symptom | Cause |
|---|---|
| cvc5 timed out on 3 of 43 obligations | `nat.toInt`/`fromInt` had bodies, so every arithmetic node became a `fromInt(toInt …)` round trip: ~2000 quantifier instantiations per query. |
| False `nat` claims returned "unknown", never a counterexample | cvc5 cannot evaluate a recursive function given only as axioms; it needs the definition (`define-fun-rec`) and its model-finding mode (`fmf-fun`). |
| The Lean stage could not start | Strata's VC generation skipped two phases, and its VC→Lean translation had no notion of datatypes. |
| Strata-Boole did not build on current Strata | Upstream moved `CallArg`; the pin was months old. |
| One obligation's replay was rejected by the kernel | A lean-smt bug — see below. |

## The changes

### Strata (`strata-org/Strata`)

| PR | What it does | Why it is needed |
|---|---|---|
| **#1471** run termCheck and precondElim in `gen_vcs` | The Lean tactic runs the same phases as the command-line verifier. | Without it `gen_smt_vcs` fails on the keynote program. |
| **#1478** opt-in `define-fun-rec` + `obligationsToVerify` | Recursive functions can be emitted as SMT definitions instead of axioms; a caller can re-check a chosen subset of obligations. Both default off. | Lets cvc5 find models, without changing the default proving encoding. Measured: only `define-fun-rec` + `fmf-fun` returns the counterexample `a = 73, b = 127`; mbqi-enum, enum-inst and sygus-inst all time out. |
| **datatypes** translate SMT datatypes to Lean inductives | Each datatype in a VC becomes a Lean `inductive` with testers and selectors, generated on the fly. | Without it no goal mentioning `nat`/`pos` reaches Lean. It also closes a gap the test suite had pinned (`mutual_recursion.lean`) and fixes a latent bug: the translator dropped state at every binder. |

### Strata-Boole

| PR | What it does | Why it is needed |
|---|---|---|
| **#14** `nat` as uninterpreted functions + axioms | No bodies; one axiom per constructor plus distribution laws (`toInt(a+b) = toInt a + toInt b`, guarded for `sub`/`div`/`mod`). | Removes the round-trip explosion — 43/43 obligations pass. Each axiom is a theorem of the old body, so nothing unsound is added. |
| **#15** migrate to current Strata | Mechanical (`CallArg` namespace, `proceduresToVerify` moved into options). | Prerequisite for the three Strata PRs. |
| **#3** re-query unknown obligations *(after #15)* | On "unknown", re-run just those obligations with bodied `nat`, `define-fun-rec` and `fmf-fun`; keep the answer only if it is a certified failure with a model. | Turns "unknown" into real counterexamples without weakening the main pass. |

### Translator (`verus-boogie`, branch `boole`)

One commit: `--nat-as-int` and its code paths removed; `nat` rendered as Boole's `nat`
at output time. Test harness fixed (an awk pattern crash) and re-run: 68 pass, 0 fail.

### lean-smt — already fixed upstream

`reconstructSumUB` recorded a sum step whose summands are all equalities as proving
`ls ≤ rs`, while the term it built proves `ls = rs`. Elaboration accepts that; the
kernel rejects whatever consumes it. Upstream fixed it in `76b4eea` (2026-08-26).

Worth stating plainly: cvc5 had *proved* that obligation. The Lean stage caught that
the replay of the proof was wrong — which is the argument for having the third stage.

## Lean version

Everything is on **Lean v4.29.1** — Strata, Strata-Boole and the translator all pin it.
lean-smt's `main` has moved to **v4.33.0**, and the `reconstructSumUB` fix lives only
there, so it is carried as a backport on a fork of lean-smt at the v4.29 commit, pinned
from `lakefile.toml`.

**A bump to v4.33 is the next infrastructure step.** It drops the fork, and has to
happen across Strata and Strata-Boole together.

## Status

- Boole + cvc5, native `nat`, generated from Rust: **43/43 obligations pass**.
- Counterexamples on false `nat` claims: working (`nat_counterexample.lean`, test 2).
- Lean kernel, native `nat`: all 43 goals generated and closed, **163 s for the file**,
  no `sorry` — most by `grind`, the rest by `smt` (cvc5's proof replayed in the kernel)
  or `inline_boole_defs; smt`, and three goals about the `pos` datatype itself by a
  short case analysis.

## Left for later

- Bump to Lean v4.33 and drop the lean-smt fork.
- Prove the nine `nat` axioms of #14 as Lean lemmas over the datatype, so the Lean
  stage assumes nothing beyond Strata's existing bridge axiom.
- Parametric datatypes in the VC→Lean translation.
- The same treatment for `--u8-as-int`.
