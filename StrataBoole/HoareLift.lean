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
top of them and Strata does not have yet. Step 2 of `docs/HoareLogic.md`.
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

end HoareLift

end -- public section
