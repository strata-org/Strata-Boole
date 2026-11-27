/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
public import Strata.Languages.Core.Logic.HoareCall
public import Strata.Languages.Core.IntEvalProps
public import Strata.Languages.Core.BoolEvalProps
public import Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.LExprDenoteEval

/-! # Lifting lemmas for the Hoare-logic route

Strata evaluates Core expressions denotationally and provides the evaluation of the integer
operators, literals, variables, equality and conditionals
(`Strata.Languages.Core.IntEvalProps`) and of the Boolean connectives
(`Strata.Languages.Core.BoolEvalProps`). This module adds what the Boole programs need on
top of them and Strata does not have yet: the Boolean of an integer equality
(`eval_eq_ints`), reading a variable of the store inside a denotation (`fvarVal_of_store`),
and a function as its body from a factory lookup (`opInterp_of_body`). Step 2 of
`docs/HoareLogic.md`; `StrataBooleTest/hoare_lift_forall.lean` is a worked example.
-/

public section

open Lambda Core

namespace HoareLift

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

/-- **Reading the store.** The valuation a store gives reads a variable as the value the
    store binds it to. -/
theorem fvarVal_of_store {tc : TyConstrInterp} [TyConstrInterp.AllInhabited tc]
    {σ : Core.CoreStore} {x : Core.Expression.Ident} {s : LSort} {v : SortDenote tc s}
    (hx : σ x = some ⟨tc, s, v⟩) :
    ValStore.fvarVal (T := Core.CoreLParams) tc σ x s = v := by
  simp [ValStore.fvarVal, hx, SemValue.read]

/-- **A function is its body.** In every model of a factory that resolves `n` to a function
    with body `body`, the function's interpretation at any arguments is the denotation of the
    body with the parameters bound to those arguments (`LFunc.InterpConsistentBody`). -/
theorem opInterp_of_body {F : Lambda.Factory Core.CoreLParams} (model : Lambda.Interp F)
    {n : String} {fn : LFunc Core.CoreLParams} (hlookup : F[n]? = some fn)
    {body : LExpr Core.CoreLParams.mono} (hbody : fn.body = some body) :
    LFunc.InterpConsistentBody model.tcInterp model.opInterp fn body := by
  have h := model.interpConsistent.1 n (Factory.getElem?_some_implies_mem hlookup) body
    (by rw [Factory.getElem?_some_getElem hlookup]; exact hbody)
  rwa [Factory.getElem?_some_getElem hlookup] at h

end HoareLift

end -- public section
