/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
public import Strata.Languages.Core.Logic.HoareCall
public import Strata.Languages.Core.IntEvalProps
public import Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.LExprDenoteEval

/-! # Lifting lemmas for the Hoare-logic route

Strata evaluates Core expressions denotationally and provides, in
`Strata.Languages.Core.IntEvalProps`, the evaluation of the integer operators, literals,
variables, equality and conditionals. This module adds what the Boole programs need on
top of it: the Boolean connectives `Bool.And` and `Bool.Or`, which Core builds as
short-circuit operators. Step 2 of `docs/HoareLogic.md`.
-/

public section

open Lambda Core

namespace HoareLift

/-! ## The connectives in `Core.Factory` -/

theorem coreFactory_boolAnd :
    (Core.Factory)["Bool.And"]? = some (Lambda.boolAndFunc (T := CoreLParams)).func := by
  have hmem : (Lambda.boolAndFunc (T := CoreLParams)).func ∈ Core.WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨Lambda.boolAndFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
  have hCore : Core.Factory = Lambda.Factory.ofArray (Core.WFFactoryArray.map (·.func)) := rfl
  rw [hCore]
  exact Lambda.Factory.get?_ofArray_of_mem hmem Core.WFFactoryArray_func_name_nodup

theorem coreFactory_boolOr :
    (Core.Factory)["Bool.Or"]? = some (Lambda.boolOrFunc (T := CoreLParams)).func := by
  have hmem : (Lambda.boolOrFunc (T := CoreLParams)).func ∈ Core.WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨Lambda.boolOrFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
  have hCore : Core.Factory = Lambda.Factory.ofArray (Core.WFFactoryArray.map (·.func)) := rfl
  rw [hCore]
  exact Lambda.Factory.get?_ofArray_of_mem hmem Core.WFFactoryArray_func_name_nodup

/-! ## Their interpretation in every consistent model

A short-circuit operator's concrete evaluation on two Boolean literals is its truth
table, so every model that is consistent with the factory interprets it that way. -/

theorem boolAnd_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Bool.And"]? = some (Lambda.boolAndFunc (T := CoreLParams)).func)
    (p q : Bool) :
    (model.opInterp "Bool.And" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool)
      = (p && q) := by
  have heval : (Lambda.boolAndFunc (T := CoreLParams)).func.concreteEval.bind
      (fun ce => ce Core.coreLoc (some ((Lambda.boolAndFunc (T := CoreLParams)).func.instTy Lambda.Subst.empty))
        [.boolConst Core.coreLoc p, .boolConst Core.coreLoc q]) =
      some (.boolConst Core.coreLoc (p && q)) := by
    cases p <;> rfl
  exact (Core.opInterp_of_concreteEval model hlookup rfl heval (fun _ => .int) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons (.const rfl) (.cons (.const rfl) .nil)) (.const rfl)).symm

theorem boolOr_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Bool.Or"]? = some (Lambda.boolOrFunc (T := CoreLParams)).func)
    (p q : Bool) :
    (model.opInterp "Bool.Or" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool)
      = (p || q) := by
  have heval : (Lambda.boolOrFunc (T := CoreLParams)).func.concreteEval.bind
      (fun ce => ce Core.coreLoc (some ((Lambda.boolOrFunc (T := CoreLParams)).func.instTy Lambda.Subst.empty))
        [.boolConst Core.coreLoc p, .boolConst Core.coreLoc q]) =
      some (.boolConst Core.coreLoc (p || q)) := by
    cases p <;> rfl
  exact (Core.opInterp_of_concreteEval model hlookup rfl heval (fun _ => .int) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons (.const rfl) (.cons (.const rfl) .nil)) (.const rfl)).symm

/-! ## Their evaluation -/

/-- `a && b` evaluates to the conjunction of the Booleans its operands evaluate to. -/
theorem eval_boolAnd {f : Core.Expression.Factory} {m m' : Core.ExpressionMetadata}
    (hlookup : f.factory["Bool.And"]? = some (Lambda.boolAndFunc (T := CoreLParams)).func)
    {σ : Core.CoreStore} {x y : Core.Expression.Expr} {p q : Bool}
    (hx : Core.Expression.eval f σ x = some (SemValue.ofBool f.model.tcInterp p))
    (hy : Core.Expression.eval f σ y = some (SemValue.ofBool f.model.tcInterp q)) :
    Core.Expression.eval f σ (.app m (.app m' Core.boolAndOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (p && q)) :=
  Core.eval_app2_op "Bool.And" (c := .bool) rfl rfl rfl hx hy
    (boolAnd_opInterp_of_lookup f.model hlookup p q)

/-- `a || b` evaluates to the disjunction of the Booleans its operands evaluate to. -/
theorem eval_boolOr {f : Core.Expression.Factory} {m m' : Core.ExpressionMetadata}
    (hlookup : f.factory["Bool.Or"]? = some (Lambda.boolOrFunc (T := CoreLParams)).func)
    {σ : Core.CoreStore} {x y : Core.Expression.Expr} {p q : Bool}
    (hx : Core.Expression.eval f σ x = some (SemValue.ofBool f.model.tcInterp p))
    (hy : Core.Expression.eval f σ y = some (SemValue.ofBool f.model.tcInterp q)) :
    Core.Expression.eval f σ (.app m (.app m' Core.boolOrOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (p || q)) :=
  Core.eval_app2_op "Bool.Or" (c := .bool) rfl rfl rfl hx hy
    (boolOr_opInterp_of_lookup f.model hlookup p q)

/-- `x == y` on two integer-valued variables evaluates to the Boolean of their equality. -/
theorem eval_eq_ints (f : Core.Expression.Factory) {m : Core.ExpressionMetadata}
    {σ : Core.CoreStore} {x y : Core.Expression.Expr} {a b : Int}
    (hx : Core.Expression.eval f σ x = some (SemValue.ofInt f.model.tcInterp a))
    (hy : Core.Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp b)) :
    Core.Expression.eval f σ (.eq m x y) = some (SemValue.ofBool f.model.tcInterp (decide (a = b))) := by
  by_cases hab : a = b
  · subst hab
    simpa using Core.eval_eq_true f hx hy
  · simpa [hab] using Core.eval_eq_false f hx hy rfl (fun h => hab (SemValue.ofInt_injective h))

end HoareLift

end -- public section
