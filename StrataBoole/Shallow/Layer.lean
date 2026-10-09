/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Do
public import Std.Tactic.Do

/-! # The shallow embedding's layer on `Std.Do`

What a Core program needs beyond Lean's `do` notation and `mvcgen`: a
nondeterministic monad with `havoc`, `assume` and `assert`, and a `while` loop
whose invariant is part of the program.  Each construct comes with its proof
rule (`@[spec]`), so `mvcgen` generates the verification conditions.

The design follows Velvet (verse-lab/velvet); the code is ours and runs on the
Lean version Strata is on.  See `docs/ShallowEmbedding.md`.
-/

public section

namespace Strata.Shallow

open Std.Do

/-- A nondeterministic computation is its set of outcomes; `none` is a failed `assert`. -/
structure ND (α : Type) where
  run : Option α → Prop

namespace ND

theorem ext {x y : ND α} (h : ∀ r, x.run r ↔ y.run r) : x = y := by
  cases x; cases y; congr; funext r; exact propext (h r)

instance : Monad ND where
  pure a := ⟨fun r => r = some a⟩
  bind x f := ⟨fun r => (∃ a, x.run (some a) ∧ (f a).run r) ∨ (x.run none ∧ r = none)⟩

theorem run_pure (a : α) (r : Option α) : (pure a : ND α).run r ↔ r = some a := Iff.rfl

theorem run_bind (x : ND α) (f : α → ND β) (r : Option β) :
    (x >>= f).run r ↔ (∃ a, x.run (some a) ∧ (f a).run r) ∨ (x.run none ∧ r = none) := Iff.rfl

instance : LawfulMonad ND := LawfulMonad.mk' ND
  (id_map := by
    intro α x; apply ext; intro r
    show (x >>= fun a => pure (id a)).run r ↔ _
    simp only [run_bind, run_pure, id]
    cases r <;> simp)
  (pure_bind := by
    intro α β a f; apply ext; intro r
    simp [run_bind, run_pure])
  (bind_assoc := by
    intro α β γ x f g; apply ext; intro r
    simp only [run_bind]
    constructor
    · rintro (⟨b, (⟨a, hx, hf⟩ | ⟨hx, hb⟩), hg⟩ | ⟨(⟨a, hx, hf⟩ | ⟨hx, -⟩), rfl⟩)
      · exact .inl ⟨a, hx, .inl ⟨b, hf, hg⟩⟩
      · cases hb
      · exact .inl ⟨a, hx, .inr ⟨hf, rfl⟩⟩
      · exact .inr ⟨hx, by simp⟩
    · rintro (⟨a, hx, (⟨b, hf, hg⟩ | ⟨hf, rfl⟩)⟩ | ⟨hx, rfl⟩)
      · exact .inl ⟨b, .inl ⟨a, hx, hf⟩, hg⟩
      · exact .inr ⟨.inl ⟨a, hx, hf⟩, rfl⟩
      · exact .inr ⟨.inr ⟨hx, by simp⟩, rfl⟩)

/-- Every outcome is a value satisfying the postcondition (partial correctness). -/
def wpTrans (x : ND α) : PredTrans .pure α where
  trans Q := ⌜∀ r, x.run r → ∃ a, r = some a ∧ (Q.1 a).down⌝
  conjunctiveRaw := by
    intro Q₁ Q₂
    simp only [SPred.bientails_nil, SPred.and_nil, SPred.down_pure]
    constructor
    · intro h
      exact ⟨fun r hr => let ⟨a, e, h1, _⟩ := h r hr; ⟨a, e, h1⟩,
             fun r hr => let ⟨a, e, _, h2⟩ := h r hr; ⟨a, e, h2⟩⟩
    · rintro ⟨h1, h2⟩ r hr
      obtain ⟨a, rfl, ha⟩ := h1 r hr
      obtain ⟨b, hb, hb2⟩ := h2 _ hr
      cases hb
      exact ⟨a, rfl, ha, hb2⟩

instance : WP ND .pure := ⟨wpTrans⟩

theorem wp_apply (x : ND α) (Q : PostCond α .pure) :
    (wp⟦x⟧ Q).down ↔ ∀ r, x.run r → ∃ a, r = some a ∧ (Q.1 a).down := Iff.rfl

private theorem spred_ext {P Q : SPred []} (h : P.down ↔ Q.down) : P = Q := by
  show ULift.up P.down = ULift.up Q.down
  rw [propext h]

instance : WPMonad ND .pure where
  wp_pure a := by
    apply PredTrans.ext; intro Q
    apply spred_ext
    rw [wp_apply]
    simp [run_pure]
  wp_bind x f := by
    apply PredTrans.ext; intro Q
    apply spred_ext
    rw [wp_apply]
    simp only [PredTrans.apply_Bind_bind, run_bind]
    show _ ↔ ∀ r, x.run r → ∃ a, r = some a ∧ ∀ r', (f a).run r' → ∃ b, r' = some b ∧ (Q.1 b).down
    constructor
    · intro h r hr
      cases r with
      | none => exact absurd (h none (.inr ⟨hr, rfl⟩)) (by simp)
      | some a => exact ⟨a, rfl, fun r' hr' => h r' (.inl ⟨a, hr, hr'⟩)⟩
    · rintro h r (⟨a, hx, hf⟩ | ⟨hx, rfl⟩)
      · obtain ⟨a', ha', h'⟩ := h _ hx
        cases ha'
        exact h' r hf
      · obtain ⟨a', ha', -⟩ := h _ hx
        cases ha'

/-! Statements Lean has no counterpart for. -/

/-- `havoc`: any value. -/
def havoc : ND α := ⟨fun r => ∃ a, r = some a⟩

/-- `assume p`: executions where `p` fails do not exist. -/
def assume (p : Prop) : ND Unit := ⟨fun r => p ∧ r = some ()⟩

/-- `assert p`: fails when `p` does not hold. -/
def assert (p : Prop) : ND Unit := ⟨fun r => (p ∧ r = some ()) ∨ (¬ p ∧ r = none)⟩

/-- Executions of `while c do body` from a state: the least relation closed under the
loop's steps, so a diverging run has no outcome (partial correctness). -/
inductive WhileRel (c : β → Prop) (body : β → ND β) : β → Option β → Prop
  | done {s} : ¬ c s → WhileRel c body s (some s)
  | step {s s' r} : c s → (body s).run (some s') → WhileRel c body s' r → WhileRel c body s r
  | fail {s} : c s → (body s).run none → WhileRel c body s none

/-- A `while` loop on the state `β`. The invariant is an annotation; it does not affect
what the loop does. -/
def whileInv (_inv : β → Prop) (c : β → Prop) (body : β → ND β) (init : β) : ND β :=
  ⟨WhileRel c body init⟩

theorem triple_iff {x : ND α} {P : Prop} {Q : α → Prop} :
    ⦃⌜P⌝⦄ x ⦃⇓ a => ⌜Q a⌝⦄ ↔ (P → ∀ r, x.run r → ∃ a, r = some a ∧ Q a) := Iff.rfl

@[spec] theorem havoc_spec : ⦃⌜True⌝⦄ (havoc : ND α) ⦃⇓ _ => ⌜True⌝⦄ := by
  rw [triple_iff]; rintro - r ⟨a, rfl⟩; exact ⟨a, rfl, trivial⟩

@[spec] theorem assume_spec (p : Prop) : ⦃⌜True⌝⦄ assume p ⦃⇓ _ => ⌜p⌝⦄ := by
  rw [triple_iff]; rintro - r ⟨hp, rfl⟩; exact ⟨(), rfl, hp⟩

@[spec] theorem assert_spec (p : Prop) : ⦃⌜p⌝⦄ assert p ⦃⇓ _ => ⌜p⌝⦄ := by
  rw [triple_iff]; rintro hp r (⟨-, rfl⟩ | ⟨hn, -⟩)
  · exact ⟨(), rfl, hp⟩
  · exact absurd hp hn

/-- The invariant rule: if the body preserves the invariant, the loop ends with the
invariant and the negated condition. -/
@[spec] theorem whileInv_spec (inv c : β → Prop) (body : β → ND β) (init : β)
    (step : ∀ s, ⦃⌜inv s ∧ c s⌝⦄ body s ⦃⇓ s' => ⌜inv s'⌝⦄) :
    ⦃⌜inv init⌝⦄ whileInv inv c body init ⦃⇓ s => ⌜inv s ∧ ¬ c s⌝⦄ := by
  rw [triple_iff]
  intro hinit r hr
  induction hr with
  | done hc => exact ⟨_, rfl, hinit, hc⟩
  | step hc hb _ ih =>
    obtain ⟨s'', hs, hinv⟩ := triple_iff.mp (step _) ⟨hinit, hc⟩ _ hb
    cases hs
    exact ih hinv
  | fail hc hb =>
    obtain ⟨s'', hs, -⟩ := triple_iff.mp (step _) ⟨hinit, hc⟩ _ hb
    cases hs

end ND

end Strata.Shallow

end
