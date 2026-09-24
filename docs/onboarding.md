# Getting started with Strata-Boole

For anyone picking up this repository. Skim it once, then run the example. The
details make more sense when something is building in front of you.

## What this is

Boole is a verification-friendly intermediate language, embedded as a DSL in
Lean and defined with Amazon's Strata framework. It is meant to read like
pseudocode, with procedures carrying `requires` and `ensures`, loops carrying
invariants, spec functions and datatypes. Source languages reach it through
trusted translations, and verification conditions come out of it as Lean goals.

It is part of the CSLib ecosystem, which is building a platform for reasoning
about code in Lean. Boole is the intermediate language that platform verifies
against.

What exists today is the Rust path:

```
Rust + Verus specs -> trusted translation -> Boole -> Core -> SMT -> cvc5
                                                      |
                                                      v
                                               Lean goals -> kernel proof
```

* **Core** is Strata's small intermediate language. Boole compiles to it, and
  the verification-condition generator and SMT encoder work on Core. This is
  the deep embedding route.
* Two back ends consume the verification conditions: **cvc5**, which is fast and
  trusted, and the **Lean kernel** via lean-smt, which is slow and trusts
  nothing, because cvc5's proof is replayed and re-checked.

Three things about that picture are expected to change, and are worth knowing
before you read the code as though it were the design.

* **Rust is one front end, not the front end.** Python, C and C++, and Java are
  intended to reach Boole the same way.
* **A shallow embedding is being explored** alongside the deep one, following
  Velvet and Loom, where a program becomes a Lean term directly rather than
  data interpreted by a generator.
* **cvc5 is one prover among several.** A Lean goal can be closed by `smt`
  (lean-smt, which calls cvc5 and replays its proof), by Lean Hammer, by
  `grind`, or by LLM-based and other AI-based provers.

Three design principles run through all of it. Boole should be readable by
humans. The tools around it should keep their trusted computing base small.
And the verification conditions should be Lean goals a person can read and
connect back to the code they came from.

## Setup

```bash
git clone <this repo> && cd Strata-Boole
lake build            # the library
lake test             # everything; takes a few minutes
```

You need `cvc5` on your `PATH` for anything that runs the solver. The Lean
version is pinned in `lean-toolchain` and `elan` will fetch it.

While iterating, build one file rather than the suite:

```bash
lake build StrataBooleTest.demo
```

## Your first program

Create `StrataBooleTest/scratch.lean`:

```lean
/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

def scratchPgm : StrataDDM.Program :=
#strata
program Boole;
procedure Increment(x : int) returns (y : int)
spec {
  requires x >= 0;
  ensures y > x;
}
{
  y := x + 1;
};
#end

#eval Strata.Boole.verify "cvc5" scratchPgm
  (options := { _root_.Core.VerifyOptions.quiet with verbose := .models })
```

Then `lake build StrataBooleTest.scratch`. You should see the one obligation,
`Increment_ensures_1_...`, pass.

Now break it. Change the body to `y := x;` and rebuild. The obligation fails and
the verifier prints a model, `(x@1, 0)`. With `x = 0` the body gives `y = 0`,
and `0 > 0` is false. That loop, writing a program, stating what should be true,
and seeing the verifier agree or disagree, is the whole job.

(`verbose := .models` is what prints the model. The pinned tests use plain
`.quiet`, which reports only pass or fail.)

The copyright header above is **required exactly as written**, blank line
included. CI rejects any `.lean` file without it.

## How tests are written

Every test is one self-contained file that states a program and *pins* what the
verifier says:

```lean
/-- info: ... -/     -- the expected output
#guard_msgs in
#eval Strata.Boole.verify "cvc5" prog (options := .quiet)
```

`#guard_msgs` compares the output against the docstring above it and fails the
build if they differ. Two things will bite you:

* Obligation labels embed **byte offsets** into the source, so inserting a line
  anywhere above shifts them and the test fails with a diff of numbers. Update
  them to whatever the build reports.
* A test file is only seen by `lake test` once `StrataBooleTest.lean` imports
  it, so add `import StrataBooleTest.<name>` there.

For the Lean back end, a test instead proves a theorem:

```lean
example : Strata.smtVCsCorrectBoole prog := by
  gen_smt_vcs_boole
  all_goals (try grind)
```

`gen_smt_vcs_boole` turns the program into one Lean goal per obligation. From
there they are ordinary Lean goals, closed by `grind`, by `omega`, or by hand.

A second route is in review. With the lean-smt dependency, `smt` sends a goal to
cvc5 and replays the returned proof in the kernel, and `inline_boole_defs`
exposes a spec function's body in a goal, the analogue of Verus's `reveal`.

## The files that matter

| File | What it does |
|---|---|
| `StrataBoole/Grammar.lean` | Boole's surface syntax, as a DDM dialect. Adding syntax starts here. |
| `StrataBoole/Boole.lean` | The AST, *generated* from the grammar by `#strata_gen`. Never edit by hand; rebuild after changing the grammar. |
| `StrataBoole/Verify.lean` | Boole → Core: `toCoreExpr`, `toCoreStmt`, `toCoreProgram`. Most work happens here. Also `Boole.verify`, which runs the solver. |
| `StrataBoole/MetaVerifier.lean` | The Lean side: `gen_smt_vcs_boole`, which turns a program into Lean goals. |
| `StrataBooleTest/` | One file per feature. `FeatureRequests/` holds tests for things not implemented yet. |
| `docs/BooleFeatureRequests.md` | What Boole supports, what it doesn't, and which test pins each. Read before picking work. |
| `AGENTS.md` | Conventions and pitfalls. Worth reading properly. |

## Adding a feature

1. **Find the gap.** `docs/BooleFeatureRequests.md` lists them with the test that
   pins current behaviour.
2. **Write the failing test first**, in `StrataBooleTest/FeatureRequests/`. Pin
   whatever happens today, even an error message. That is how we track what is
   missing, and it becomes the regression test for free.
3. **Syntax, if needed**: add an `op` or `fn` to `Grammar.lean`, then
   `lake build StrataBoole.Boole` to regenerate the AST.
4. **Lowering**: add the case to `toCoreExpr` or `toCoreStmt`. Copy how a
   neighbouring construct does it. The translation state (`bvars`,
   `modifiesMap`, ...) has invariants that are easier to imitate than to
   rediscover.
5. **Check both back ends**: `#eval Strata.Boole.verify "cvc5"` is the fast loop;
   add a `gen_smt_vcs_boole` block if the feature should work in the kernel too.
6. `lake test`, then a PR.

If a task turns out to be blocked on something Strata itself doesn't support,
say so and stop. That is a real result, and it belongs in
`BooleFeatureRequests.md`; several entries there ended exactly that way.

## Things that will confuse you once

* **Global variables are not real.** Boole `var` declarations and `modifies`
  clauses become extra parameters on every procedure and call site. See
  `getGlobalParamPrefix`.
* **`old(x)` only means anything for `inout` parameters.** Elsewhere
  `old x = x`.
* **`Boole.lean` is expensive to rebuild** (`maxHeartbeats 400000`). Avoid
  touching `Grammar.lean` casually.
* **Spec functions reach the solver as opaque names.** That is deliberate; it
  keeps queries small. A goal that needs a body has to ask for it.

## Further reading

* The CSLib website, <https://cslib.io>, and the whitepaper,
  <https://arxiv.org/abs/2602.04846>, for what the wider project is doing and
  why Boole sits where it does in it.
* The Zulip channels `#CSLib` and `#CSLib: Code Reasoning` on
  <https://leanprover.zulipchat.com>, which are where design questions get
  settled.
* [Lean-SMT](https://github.com/ufmg-smite/lean-smt), the tactic behind the
  kernel back end. It hands a goal to cvc5 and reconstructs the returned proof
  in Lean, so the solver does not have to be trusted.
* Velvet and Loom, for the shallow embedding mentioned above. Loom is
  [*Foundational Multi-Modal Program Verifiers*](https://ilyasergey.net/assets/pdf/papers/loom-preprint.pdf),
  and [Velvet](https://ilyasergey.net/assets/pdf/papers/velvet-cav26.pdf) is the
  Dafny-style verifier built on it.
* [A tutorial on Lean's `vcgen`](https://github.com/ilyasergey/lean-vcgen-tutorial),
  which builds a small verifier the deep-embedding way and is the quickest route
  to understanding how verification conditions are produced.
