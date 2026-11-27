/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.HoareLift
public import Strata.Languages.Core.SeqEvalProps
public import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteCompute
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.LExprWF

/-! # Lifting a quantified clause: a worked example

A contract clause of the Hoare-logic route is a Core expression that evaluates to `true`
in a store. Lifting turns that fact into a proposition over Lean values. This file does it
by hand, once, for the clause

    forall j : int :: 0 <= j && j < Sequence.length(s) ==> ok(Sequence.select(s, j))

which has the shape of the quantified `requires` and loop invariant of
`dalek_sum_of_slice`, with a user function `ok` in the place of `is_canonical_scalar`.
`all_lift` concludes that `ok` holds of every element of the sequence in range.

The five steps of its proof are the ones a lifting tactic has to automate
(step 2 of `docs/HoareLogic.md`):

1. evaluation to `true` is the denotation being `true` (`LExpr.denoteEval_eq_ofBool_iff`);
2. the store types the variables as the clause does, so annotating changes nothing
   (`LExpr.annotateFvars_eq_self`);
3. the `denotes` tactic computes the denotation: a quantifier becomes a Lean `∀`, and the
   body a term in the model's operators (`denote_true_iff_of_Denotes`);
4. a variable read from the store is the value the store holds
   (`HoareLift.fvarVal_of_store`);
5. the built-in operators are their Lean operations (the `_opInterp_of_lookup` lemmas of
   Strata's `IntEvalProps` and `BoolEvalProps`).

A user function stays an operator of the model here. `HoareLift.opInterp_of_body` replaces
it by its body where a proof needs that.

The `denotes` tactic and its lemmas are internal to Strata's denotation modules, so lifting
code has to live in a module that imports them with `import all`, as this file does.
-/

public section

namespace HoareLiftForall

open Lambda

abbrev L := Core.valueLoc
abbrev seqInt : LMonoTy := .tcons "Sequence" [LMonoTy.int]
abbrev sId : Core.Expression.Ident := ⟨"s", ()⟩
abbrev sV : Core.Expression.Expr := .fvar L sId (some seqInt)
abbrev b0 : Core.Expression.Expr := .bvar L 0
abbrev opE (n : String) (ty : LMonoTy) : Core.Expression.Expr := .op L ⟨n, ()⟩ (some ty)
abbrev bool2 : LMonoTy := .arrow .bool (.arrow .bool .bool)
abbrev int2b : LMonoTy := .arrow LMonoTy.int (.arrow LMonoTy.int .bool)

/-- `0 <= j && j < length(s) ==> ok(select(s, j))`, under the binder of `j`. -/
abbrev allBody : Core.Expression.Expr :=
  .app L (.app L (opE "Bool.Implies" bool2)
    (.app L (.app L (opE "Bool.And" bool2)
      (.app L (.app L (opE "Int.Le" int2b) (.intConst L 0)) b0))
      (.app L (.app L (opE "Int.Lt" int2b) b0)
        (.app L (opE "Sequence.length" (.arrow seqInt LMonoTy.int)) sV))))
    (.app L (opE "ok" (.arrow LMonoTy.int .bool))
      (.app L (.app L (opE "Sequence.select" (.arrow seqInt (.arrow LMonoTy.int LMonoTy.int))) sV) b0))

abbrev allE : Core.Expression.Expr := .quant L .all "j" (some LMonoTy.int) b0 allBody

/-- **A quantified clause as a Lean `∀`.** If the clause evaluates to `true` in a store that
    binds `s` to the sequence `sv`, then `ok` holds of every element of `sv` in range. -/
theorem all_lift (Fm : Core.Expression.Factory) (σ : Core.CoreStore)
    (himp : Fm.factory["Bool.Implies"]? = some (Lambda.boolImpliesFunc (T := Core.CoreLParams)).func)
    (hand : Fm.factory["Bool.And"]? = some (Lambda.boolAndFunc (T := Core.CoreLParams)).func)
    (hle : Fm.factory["Int.Le"]? = some (Lambda.intLeFunc (T := Core.CoreLParams)).func)
    (hlt : Fm.factory["Int.Lt"]? = some (Lambda.intLtFunc (T := Core.CoreLParams)).func)
    (sv : SortDenote Fm.model.tcInterp (.tcons "Sequence" [.int]))
    (hs : σ sId = some ⟨Fm.model.tcInterp, .tcons "Sequence" [.int], sv⟩)
    (h : Core.Expression.eval Fm σ allE = some (SemValue.ofBool Fm.model.tcInterp true)) :
    ∀ j : Int, 0 ≤ j → j < Core.seqLengthOf Fm.model .int sv →
      (Fm.model.opInterp "ok" (LSort.mkArrow .bool [.int])
        (Core.seqSelectOf Fm.model .int sv j) : Bool) = true := by
  -- 1. Evaluation to `true` is the denotation being `true`.
  obtain ⟨hdef, hty, hden⟩ := (LExpr.denoteEval_eq_ofBool_iff (T := Core.CoreLParams)).mp h
  -- 2. The store types `s` as the clause does, so its annotation changes nothing.
  have hann : allE.annotateFvars (ValStore.ann σ) = allE :=
    LExpr.annotateFvars_eq_self allE (by
      intro x ty hx
      simp only [LExpr.freeVars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq, or_self, List.nil_append] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨seqInt, rfl, by simp only [ValStore.ann, hs, Option.map_some]; rfl⟩)
  revert hty hden
  rw [hann]
  intro hty hden
  letI := Fm.model.allInhabited
  -- 3. The quantifier is a Lean `∀`; its body is a term in the model's operators.
  have hv := Eq.mp (denote_true_iff_of_Denotes (by denotes)) hden
  rw [classical_decide_eq_true] at hv
  intro j h0 hj
  have hb := Eq.mp (denote_true_iff_of_Denotes (by denotes)) (hv j)
  -- 4. The store read of `s` is the sequence it holds.
  have hfv : ValStore.fvarVal (T := Core.CoreLParams) Fm.model.tcInterp σ sId
      (LSort.tcons "Sequence" [LSort.int]) = sv := HoareLift.fvarVal_of_store hs
  dsimp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map, denoteConst, LConst.ty] at hb
  rw [hfv] at hb
  -- 5. The built-in operators are their Lean operations.
  have e1 := Core.intLe_opInterp_of_lookup Fm.model hle 0 j
  have e2 := Core.intLt_opInterp_of_lookup Fm.model hlt j (Core.seqLengthOf Fm.model .int sv)
  have e3 := Core.boolAnd_opInterp_of_lookup Fm.model hand (decide (0 ≤ j))
    (decide (j < Core.seqLengthOf Fm.model .int sv))
  have e4 := Core.boolImplies_opInterp_of_lookup Fm.model himp
    (decide (0 ≤ j) && decide (j < Core.seqLengthOf Fm.model .int sv))
    (Fm.model.opInterp "ok" (LSort.mkArrow .bool [.int]) (Core.seqSelectOf Fm.model .int sv j))
  dsimp only [LSort.mkArrow, List.foldr, Core.seqLengthOf, Core.seqSelectOf, LSort.int,
    LSort.bool] at e1 e2 e3 e4 hb ⊢
  rw [e1, e2, e3, e4] at hb
  have h0' : decide (0 ≤ j) = true := decide_eq_true h0
  have hj' := decide_eq_true hj
  dsimp only [Core.seqLengthOf, LSort.mkArrow, List.foldr, LSort.int] at hj'
  rw [h0', hj'] at hb
  exact hb

end HoareLiftForall

end -- public section
