/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Shallow.Layer

/-! Three programs, written by hand in the form the translation from Core
should produce, verified with `mvcgen` on the layer.  This file is the
contract between the translation and the layer. -/

-- Lean marks `mvcgen` experimental; see docs/ShallowEmbedding.md.
set_option mvcgen.warning false

namespace Strata.Shallow.Test

open Std.Do Strata.Shallow Strata.Shallow.ND

/-- `havoc x; assume x >= 0`. -/
def pick_nat : ND Int := do
  let x ← havoc
  assume (x ≥ 0)
  return x

theorem pick_nat_spec : ⦃⌜True⌝⦄ pick_nat ⦃⇓ x => ⌜x ≥ 0⌝⦄ := by
  mvcgen [pick_nat]

/-- A loop without a termination measure.  State: `(i, r)`. -/
def sum_to (n : Int) : ND Int := do
  let s ← whileInv
    (fun s : Int × Int => 0 ≤ s.1 ∧ s.1 ≤ n ∧ 2 * s.2 = s.1 * (s.1 + 1))
    (fun s => s.1 < n)
    (fun s => pure (s.1 + 1, s.2 + (s.1 + 1)))
    (0, 0)
  return s.2

theorem sum_to_spec (n : Int) (h : n ≥ 0) :
    ⦃⌜True⌝⦄ sum_to n ⦃⇓ r => ⌜2 * r = n * (n + 1)⌝⦄ := by
  mvcgen [sum_to]
  all_goals grind

/-- Find max, from the Verus translator's Boole output.  State: `(max, i)`. -/
def find_max (nums : Array (BitVec 32)) : ND (BitVec 32) := do
  assert (0 < nums.size)
  let s ← whileInv
    (fun s : BitVec 32 × Int =>
      (∃ j : Int, 0 ≤ j ∧ j < s.2 ∧ s.1 = nums[j.toNat]!) ∧
      (∀ k : Int, 0 ≤ k ∧ k < s.2 → BitVec.sle nums[k.toNat]! s.1) ∧
      0 ≤ s.2 ∧ s.2 ≤ nums.size)
    (fun s => s.2 < nums.size)
    (fun s => do
      assert (0 ≤ s.2 ∧ s.2 < nums.size)
      let max := if BitVec.slt s.1 nums[s.2.toNat]! then nums[s.2.toNat]! else s.1
      assert (0 ≤ s.2 + 1 ∧ s.2 + 1 ≤ 18446744073709551615)
      pure (max, (s.2 + 1) % 18446744073709551616))
    (nums[0]!, 1)
  return s.1

theorem find_max_spec (nums : Array (BitVec 32)) :
    ⦃⌜nums.size > 0 ∧ (nums.size : Int) ≤ 18446744073709551615⌝⦄
    find_max nums
    ⦃⇓ ret => ⌜(∀ i : Int, 0 ≤ i ∧ i < nums.size → BitVec.sle nums[i.toNat]! ret) ∧
               (∃ j : Int, 0 ≤ j ∧ j < nums.size ∧ ret = nums[j.toNat]!)⌝⦄ := by
  mvcgen [find_max]
  all_goals (try simp only [BitVec.sle_iff_toInt_le] at *)
  all_goals (try grind)
  -- One iteration: the invariant holds again.
  · rename_i hpre _ h0 s _ max hb _ hov hinv
    obtain ⟨⟨⟨j, hj0, hji, hmax⟩, habove, hi0, hin⟩, hlt⟩ := hinv
    have hmaxdef : max = if s.1.slt nums[s.2.toNat]! = true then nums[s.2.toNat]! else s.1 := rfl
    clear_value max
    subst hmaxdef
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    refine ⟨?_, ?_, by omega, by omega⟩
    · split
      · exact ⟨s.2, by omega, by omega, rfl⟩
      · exact ⟨j, hj0, by omega, hmax⟩
    · intro k hk0 hk
      split
      · next hslt =>
        rw [BitVec.slt_iff_toInt_lt] at hslt
        by_cases hki : k < s.2
        · have := habove k hk0 hki
          omega
        · obtain rfl : k = s.2 := by omega
          exact Int.le_refl _
      · next hslt =>
        rw [BitVec.slt_iff_toInt_lt] at hslt
        by_cases hki : k < s.2
        · exact habove k hk0 hki
        · obtain rfl : k = s.2 := by omega
          omega
  -- Entry: the prefix is just `nums[0]`.
  · rename_i hpre _ h0
    refine ⟨⟨0, by omega, by omega, by simp⟩, ?_, by omega, by exact_mod_cast h0⟩
    intro k hk0 hk
    obtain rfl : k = 0 := by omega
    simp

/-- info: 'Strata.Shallow.Test.pick_nat_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pick_nat_spec

/-- info: 'Strata.Shallow.Test.sum_to_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_to_spec

/-- info: 'Strata.Shallow.Test.find_max_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms find_max_spec

end Strata.Shallow.Test
