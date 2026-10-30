/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! # A generic model of datatypes

One Lean inductive of constructor applications interprets every datatype of
every program, so the interpreter knows a single type and nothing is generated
per program.  The datatype laws (disjointness, injectivity, inversion) are
proved once; induction is recursion on the term.  `pos` and `nat` from Boole's
`nat` library serve as the example.

Not covered yet: `Map` fields keyed by a datatype (a negative occurrence) and
parametric datatypes.  See `docs/HoareLogic.md`.
-/

mutual
inductive DT : Type where
  | mk (ctor : String) (args : List Arg)
inductive Arg : Type where
  | int (i : Int)
  | bool (b : Bool)
  | dt (d : DT)
end

namespace DT

inductive ArgSort | int | bool | dt (name : String)
abbrev Sig := String → List (String × List ArgSort)

mutual
inductive WS (sig : Sig) : String → DT → Prop where
  | mk {d c args sorts} : (c, sorts) ∈ sig d → WSArgs sig sorts args → WS sig d (DT.mk c args)
inductive WSArgs (sig : Sig) : List ArgSort → List Arg → Prop where
  | nil : WSArgs sig [] []
  | int {i ss as} : WSArgs sig ss as → WSArgs sig (.int :: ss) (.int i :: as)
  | bool {b ss as} : WSArgs sig ss as → WSArgs sig (.bool :: ss) (.bool b :: as)
  | dt {name v ss as} : WS sig name v → WSArgs sig ss as → WSArgs sig (.dt name :: ss) (.dt v :: as)
end

/-- The carrier of datatype `d`: its well-sorted values. -/
def Carrier (sig : Sig) (d : String) := { v : DT // WS sig d v }

/-! The datatype laws, once, for all signatures. -/

theorem disjoint {c c' : String} {as as' : List Arg} (h : c ≠ c') : DT.mk c as ≠ DT.mk c' as' := by
  intro e; cases e; exact h rfl

theorem injective {c : String} {as as' : List Arg} (h : DT.mk c as = DT.mk c as') : as = as' := by
  cases h; rfl

theorem inversion {sig : Sig} {d : String} {v : DT} (h : WS sig d v) :
    ∃ c args sorts, v = DT.mk c args ∧ (c, sorts) ∈ sig d ∧ WSArgs sig sorts args := by
  cases h with
  | mk hc hargs => exact ⟨_, _, _, rfl, hc, hargs⟩

/-! `pos = xH | xO pos | xI pos`, `nat = N0 | Npos pos` on the generic model. -/

def posSig : Sig
  | "pos" => [("xH", []), ("xO", [.dt "pos"]), ("xI", [.dt "pos"])]
  | "nat" => [("N0", []), ("Npos", [.dt "pos"])]
  | _ => []

def is_xO : DT → Prop | .mk "xO" [_] => True | _ => False
def xO_h : DT → DT | .mk "xO" [.dt h] => h | _ => .mk "xH" []

/-- `pos.toInt` by structural recursion on the generic term. -/
def posToInt : DT → Int
  | .mk "xH" [] => 1
  | .mk "xO" [.dt h] => 2 * posToInt h
  | .mk "xI" [.dt h] => 2 * posToInt h + 1
  | _ => 0

example : posToInt (.mk "xI" [.dt (.mk "xO" [.dt (.mk "xH" [])])]) = 5 := by decide

example : Carrier posSig "pos" := ⟨.mk "xH" [], .mk (by simp [posSig]) .nil⟩
example : Carrier posSig "nat" := ⟨.mk "N0" [], .mk (by simp [posSig]) .nil⟩

/-- A well-sorted `pos` is `xH`, or `xO`/`xI` of a well-sorted `pos`. -/
theorem pos_cases {v : DT} (h : WS posSig "pos" v) :
    v = .mk "xH" [] ∨ (∃ h', WS posSig "pos" h' ∧ (v = .mk "xO" [.dt h'] ∨ v = .mk "xI" [.dt h'])) := by
  cases h with
  | mk hc hargs =>
    simp [posSig] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hargs; exact .inl rfl
    · cases hargs with | dt hv hrest => cases hrest; exact .inr ⟨_, hv, .inl rfl⟩
    · cases hargs with | dt hv hrest => cases hrest; exact .inr ⟨_, hv, .inr rfl⟩

/-- Induction over `pos`: recursion on the term size, using `pos_cases`. -/
theorem posToInt_pos (v : DT) (hw : WS posSig "pos" v) : 0 < posToInt v := by
  rcases pos_cases hw with e | ⟨h', hh', e | e⟩ <;> rw [e]
  · simp [posToInt]
  · have := posToInt_pos h' hh'; simp [posToInt]; omega
  · have := posToInt_pos h' hh'; simp [posToInt]; omega
termination_by sizeOf v
decreasing_by all_goals (subst e; simp_wf; (try simp); omega)

end DT
