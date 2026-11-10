# Verifying Boole programs in Lean

## Goal

Verify Boole programs in Lean with proofs that are sound by construction. Today's Lean
path trusts the VC generator, the SMT encoding and a bridge axiom; strata-org/Strata#1488
showed it could prove `False`, and strata-org/Strata#1490 closed that by refusing every
VC the denotation does not cover. Here the trusted parts are Core's semantics and Lean, and the
goals range over Lean values, so Lean tactics work on them without a solver. Boole programs
reach it through their lowering to Core.

```mermaid
flowchart TD
    B["Boole program"] -->|toCoreProgram| C["Strata Core program"]
    subgraph solver ["Solver path"]
        V["VC generation and SMT encoding"] --> S["cvc5, or Lean via lean-smt"]
    end
    subgraph lean ["Lean path"]
        H["Core.Logic.Hoare: contract as a triple"] --> T["tactic applies the proved rules"]
        T --> G["lifted goals over Lean values"] --> P["Lean proof"]
    end
    C --> V
    C --> H
    O["Core operational semantics"] -. rules are theorems about it .- H
```

## What Strata already provides

`Strata/Languages/Core/Logic/` (on Strata `main` since September 2026) is a Hoare logic for
Core over Core's own operational semantics:

- `Core.Logic.Hoare.Triple π params Pre ss Post factory`, quantified over every model
  of `factory` (`Lambda.Interp`). A model satisfies the factory's axioms, and
  `Core.factoryInterp` is one (maps as functions, sequences as lists, sets as predicates),
  so the triple is never vacuous.
- Proved rules for `cmd`, `set`, `init`, `seq`, `block`, `exit_cons`, `ite`, `while_rule`
  (partial correctness) and `Procedure.call_of_contract`.
- `Procedure.contractTriple`, which reads `requires` and `ensures` as the triple to prove,
  with `old` snapshots, typed parameters and typed clauses, over the factory visible at
  the procedure: Core's operators plus the functions declared before it
  (`Program.factoryBeforeProcedure`). The generic `SpecHoareConnection`
  (`Strata/DL/Imperative/Logic/`) relates a triple to Strata's own notion of assertion
  validity.
- Expressions are evaluated denotationally (since November 2026): `Expression.eval` is
  `LExpr.denoteEval` over the factory, a model of it and the sorts of its type variables,
  and stores hold semantic values.
- Lifting lemmas for the `int` and `bv` operators, free variables, `==` and `if`
  (`IntEvalProps.lean`, `BitVecEvalProps.lean`): the evaluator on values is the Lean
  operation in every model.

Its tests prove some twenty procedures by applying the rules by hand, with `native_decide`
for facts about the AST. There is no automation: a goal reads
`Expression.eval ρ.factory ρ.store e = some v` until the lemmas are applied.

Its authors confirmed (October 2026) that the triple was written as the specification of
partial correctness, the invariant a correct program transformation must preserve, and
that they have no plans to automate it. Generating verification conditions against it is
open to others, and they see no blocker once the generator's correctness is established.
So the tactic below is ours to build, and the triple is a stable target.

## Plan

1. **VC generation tactic over `Core.Logic.Hoare`.** From `Procedure.contractTriple p params
   name`, apply the rules backwards statement by statement and discharge their side
   conditions (`InitEnvWF`, `PostWF`, `exitsCoveredByBlocks`) by evaluation on the
   concrete AST. The result is one goal per `assert`, loop invariant and `ensures`, over
   the store. This is the shape of `core_vcgen` in the `StrataBoole/Deep/` experiment (fork
   branch `exp/deep-embedding`), retargeted from its own `Exec` to Strata's `Triple`.
2. **Lifting.** Turn each goal into a proposition over Lean values: a store slot of type
   `int` is an `Int` (`inputAsPredicate` and `SemValue.exists_ofInt`), `Expression.eval`
   of an operator on values is the Lean operation (Strata's lemmas, plus ours for the
   Boolean connectives and `==` in `StrataBoole/HoareLift.lean`), and a contract clause
   becomes the corresponding proposition. Still to write: the lemmas for `Map` and
   `Sequence` operators, which follow from the factory axioms, and for quantifiers. This
   is the shape of `core_lift`. Milestone:
   `max2`, then the counting loop of `demo.lean`, then `find_max`, proved by the tactic,
   lifting, and `omega`/`grind`.
3. **Boole entry.** The prototype's `shallow_reflect` (on its fork branch) already produces
   the type-checked Core program as a Lean term. It is the input of step 1, so a user
   writes a `#strata program Boole` block and states `contractTriple` on its procedures.
4. **Gaps shared with Strata, fixed in Strata.** Rules for nondeterministic `if` and
   `while`; the program's uninterpreted functions and axioms in the model (its functions
   with bodies are in since November 2026); the generic datatype carrier wired into the
   model (decision below), which also covers `nat`.
5. **Boole semantics.** A Boole interpreter proved to agree with `toCoreProgram`, so that
   Boole has a meaning stated in its own terms and the lowering to Core is proved correct
   rather than definitional. This is what makes Boole a language rather than a front end.
   It comes after steps 1 to 3 because the agreement theorem needs Core's semantics on the
   other side. Its prerequisites, `toCoreExpr` total and the `nat` library inside
   `typeCheck`, are merged (strata-org/Strata-Boole#25, #26). Running programs is not
   what it is for: Strata already has an executable evaluator for Core
   (`Strata/Languages/Core/StatementEval.lean`). Open design choice: Velvet's
   nondeterministic state monad, with its VC generator, is a candidate for the
   interpreter now that Strata and Velvet share a Lean version.

## Decisions

- Build on `Core.Logic.Hoare`, not on a semantics of our own: neither `Deep/`'s `Exec`,
  which nothing connects to Core's semantics, nor an interpreter with an adequacy proof
  that would redo what Strata's rules already prove.
- Core first, then Boole. Boole is the language users write and the one this work is
  about; Core is where the proved semantics lives today. Starting from Boole directly
  would leave nothing to prove adequacy against, so the Boole semantics is step 5, not
  step 1.
- Goals over Lean values come from lifting, not from a monadic encoding, so
  `Std.Do`/`mvcgen` (`StrataBoole/Shallow/Layer.lean`) is off the path.
- Failure is never vacuous: a construct the tactic cannot handle leaves the goal open
  instead of closing it.
- Datatypes get one generic model, not one Lean inductive per program: a single inductive
  of constructor applications with a well-sortedness predicate (`DT.Carrier` in
  `Strata/DL/SMT/DenoteDatatypes.lean`, the SMT denotation under review in Strata). Its laws
  are proved once, a program's datatypes are declarations the model reads, and `nat` is
  its `pos`/`nat` with `toInt` by structural recursion. The same carrier interprets
  datatype sorts in the model `Triple` quantifies over, which discharges the laws the
  Lambda denotation leaves as assumptions. The per-program inductives of
  strata-org/Strata#1480 serve the SMT-IR path; readable goals (`pos.xO h` for
  `mk "xO" [h]`) are notation and simp lemmas added later.
- This is a deep embedding with shallow goals: the program stays data, the Lean term is
  the proof about it, and what the user sees are goals over Lean values. It started as a
  shallow embedding in the Velvet sense; say so when the difference matters. The
  `Shallow` names left in the tree (`StrataBoole/Shallow/`, `shallow_find_max`) are that
  prototype's.

## Coverage of the rules

| Core | `Core.Logic.Hoare` |
| --- | --- |
| assignments, `init`, `assert`, `assume`, `havoc` (as `set x *` through `cmd`), blocks, `exit`, deterministic `if` and `while`, `call` | rules exist |
| `if *`, `while *`, loop measures, `cover` | to add |
| `int`, `bool`, `bv n` | denoted and lifted |
| `Map`, `Sequence`, `Set`, `string` operators | modelled, every model satisfies their axioms; lifting lemmas to add (step 2) |
| datatypes, `nat` | generic carrier (decision above); wiring into the model is step 4 |
| user functions with bodies | in the model (`factoryBeforeProcedure`) |
| uninterpreted functions, `axiom` | step 4 |

## Target: the benchmark the solver path already verifies

`StrataBooleTest/dalek_sum_of_slice.lean` (36 obligations, cvc5 and lean-smt) is the
program this route has to reach. What it uses, and where each item sits:

| In the program | Needs | Step |
| --- | --- | --- |
| `for` loop with six invariants, `call` in the body, `exit` | rules exist; the tactic must discharge the loop and call side conditions | 1 |
| integer and `bv W8` arithmetic, `as_uint`, comparisons | lifting lemmas per operator | 2 |
| quantified `requires` and invariants | lifting of quantifiers to Lean `∀` over `Int` | 2 |
| `Sequence (bv W8)` and `Sequence Scalar`, `select`, `length` | lifting lemmas from the sequence axioms | 2 |
| native `nat`, the `nat_*` library | the generic carrier in the model, library functions as program functions | 4 |
| `function` definitions, one `rec function` with `requires` and `decreases` | in the model | done |
| `function f();` without body | uninterpreted functions in the model | 4 |
| `axiom` declarations, including the unfolding axiom of the recursive function | program axioms as hypotheses on the model | 4 |
| a callee whose body is `assume false` | `call_of_contract` with a trivially proved contract | 1 |

The lifted goals must stay solver-friendly: lean-smt closes goals over `Int`, `Bool` and
`BitVec`, so sequences should lift to a length and an index function rather than to
`List`, and `nat` to `Nat`. Decide this with step 4; it does not affect steps 1 to 3.

Order: `max2`, the counting loop, then this program as soon as step 4 lands in Strata.
Everything in steps 1 to 3 is exercised by the first two and reused unchanged by the third.

## Status

- `max2` is proved against Strata's triple, by hand, in `StrataBooleTest/hoare_max2.lean`
  on the denotational semantics: `contractTriple_of_core_typed`, then `block`, `block`,
  `ite` and `set`, every side condition by `native_decide` on the reflected program, the
  inputs recovered from the condition's evaluation (`denoteEval_defines`), the operators
  lifted with Strata's `eval_intGe` and `eval_fvar_int` and our `eval_boolAnd`,
  `eval_boolOr` and `eval_eq_ints` (`StrataBoole/HoareLift.lean`, each from the model's
  agreement with the operator's concrete evaluation). The proof is the specification of
  the step 1 tactic: it does these steps for any straight-line body with `if`. Steps 1
  and 2 as automation: not started. `Deep/` has both against its own semantics, with
  `max2` and a counting loop proved.
- `StrataBoole/Shallow/Layer.lean` is kept until the milestone is reached.
- Two things the hand proof settled. Under the module system, facts about factory entries
  are not `rfl`; they need `import all` of the defining files and `simp` unfolding. And
  the typing derivations (`HasTypeA`) must be spelled with the annotations exactly as the
  lowering writes them, or the rewrite rules do not fire; the tactic should build them
  from the term, not from the types.
- `StrataBooleTest/generic_datatypes.lean`: first prototype of the carrier.
- Risks. Strata's own hand proof of a two-branch `if` is some twenty-five lines with
  `native_decide` and explicit store facts, so discharging the side conditions
  automatically is the bulk of step 1.
- `Map` and `Sequence` were outside the logic until November 2026 (strata-org/Strata#1496:
  their operators had no execution, and models were free to violate the axioms). The
  denotational evaluation fixed both; what remains is the lifting lemmas of step 2.

## Open questions

- Loop measures: `while_rule` is partial correctness. Add a total-correctness rule, or
  check `decreases` separately?
- `cover` is a reachability check, not a Hoare fact. How to state it?
- Goal names: carry the program's clause names into the goals the tactic leaves.
- `native_decide` for AST facts: acceptable in the tactic, or avoid it?

## Sources

- [Velvet (CAV'26)](https://ilyasergey.net/assets/pdf/papers/velvet-cav26.pdf)
- [Foundational Multi-Modal Program Verifiers (Loom, POPL'26)](https://ilyasergey.net/assets/pdf/papers/loom-popl26.pdf)
- [ilyasergey/lean-vcgen-tutorial](https://github.com/ilyasergey/lean-vcgen-tutorial)
