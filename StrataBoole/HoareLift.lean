/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
public import Strata.Languages.Core.Logic.HoareCall
public import Strata.Languages.Core.Factory
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Util.FuncAttr
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.Denote.LExprDenote

/-! # Lifting lemmas for the Hoare-logic route

Facts about Core's evaluator on the operators a program uses, stated so that a
goal left by Core's Hoare rules (`Expression.eval ρ.store e = some v`) becomes a
proposition over Lean values. Step 2 of `docs/HoareLogic.md`. Each operator gets
one block like the `Int.Ge` one below.
-/

public section

open Lambda Core

namespace HoareLift

abbrev E := Core.Expression.Expr

/-! ## Literals and variables -/

theorem isValue_intConst (a : Int) : LExpr.isValue Core.Factory (LExpr.intConst () a : E) = true :=
  Lambda.isValue_const_true _ _ _

theorem eval_const (n : Nat) (env : Lambda.Env CoreLParams) (m : Unit) (κ : LConst) :
    LExpr.eval n Core.Factory env (.const m κ) = (.const m κ, .value true) := by
  cases n <;> simp [LExpr.eval, Lambda.isValue_const_true]

/-- Core's expression metadata is `Unit`, so every metadata is `()`. -/
theorem unit_metadata (e : E) : LExpr.metadata e = () := rfl

theorem eval_intConst (n : Nat) (env : Lambda.Env CoreLParams) (a : Int) :
    LExpr.eval n Core.Factory env (.intConst () a) = (.intConst () a, .value true) :=
  eval_const n env () _

theorem eval_boolConst (n : Nat) (env : Lambda.Env CoreLParams) (b : Bool) :
    LExpr.eval n Core.Factory env (.boolConst () b) = (.boolConst () b, .value true) :=
  eval_const n env () _

theorem callOfLFunc_fvar_partial_none (x : Core.Expression.Ident) (ty : Option LMonoTy) :
    Core.Factory.callOfLFunc (LExpr.fvar () x ty : E) (allowPartialApp := true) = none := by
  simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]

theorem isValue_fvar_false' (x : Core.Expression.Ident) (ty : Option LMonoTy) :
    LExpr.isValue Core.Factory (LExpr.fvar () x ty : E) = false := by
  rw [LExpr.isValue.eq_def]
  split <;> (try (rename_i h; simp at h))
  split
  · rename_i h; rw [callOfLFunc_fvar_partial_none] at h; cases h
  · rfl

/-- A variable bound to a value evaluates to it in one step. -/
theorem eval_fvar_value (env : Lambda.Env CoreLParams) (x : Core.Expression.Ident)
    (ty : Option LMonoTy) (v : E) (hx : env x = some v) (hv : LExpr.isValue Core.Factory v = true) :
    LExpr.eval 1 Core.Factory env (.fvar () x ty) = (v, .value true) := by
  show LExpr.eval (Nat.succ 0) Core.Factory env _ = _
  rw [LExpr.eval.eq_2 (TBase := CoreLParams), isValue_fvar_false']
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Lambda.callOfLFunc_fvar_none]
  simp only [LExpr.evalCore, hx, hv, ↓reduceIte]

/-! The empty attribute array answers every attribute query negatively. -/

theorem attr_findInlineIfConstr_empty :
    Strata.DL.Util.FuncAttr.findInlineIfConstr (#[] : Array Strata.DL.Util.FuncAttr) = none := by
  simp [Strata.DL.Util.FuncAttr.findInlineIfConstr]
theorem attr_findEvalIfConstr_empty :
    Strata.DL.Util.FuncAttr.findEvalIfConstr (#[] : Array Strata.DL.Util.FuncAttr) = none := by
  simp [Strata.DL.Util.FuncAttr.findEvalIfConstr]
theorem attr_findEvalIfValue_empty :
    Strata.DL.Util.FuncAttr.findEvalIfValue (#[] : Array Strata.DL.Util.FuncAttr) = none := by
  simp [Strata.DL.Util.FuncAttr.findEvalIfValue]
theorem attr_hasInlineIfAllValues_empty :
    Strata.DL.Util.FuncAttr.hasInlineIfAllValues (#[] : Array Strata.DL.Util.FuncAttr) = false := by
  simp [Strata.DL.Util.FuncAttr.hasInlineIfAllValues]
theorem attr_contains_inline_empty :
    (#[] : Array Strata.DL.Util.FuncAttr).contains .inline = false := by simp

/-! ## `Int.Ge` -/

/-- `Int.Ge a b`, as the lowering of `a >= b` writes it. -/
def intGe (a b : E) : E :=
  .app () (.app () (.op () ⟨"Int.Ge", ()⟩ (some (.arrow .int (.arrow .int .bool)))) a) b

set_option maxRecDepth 4000 in
theorem intGeFunc_mem : (Lambda.intGeFunc : WFLFunc CoreLParams) ∈ Core.WFFactoryArray := by
  rw [Array.mem_def]
  unfold Core.WFFactoryArray
  simp only [Array.toList_appendList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, true_or, or_true]

theorem factory_get_intGe :
    Core.Factory.get? "Int.Ge" = some (Lambda.intGeFunc : WFLFunc CoreLParams).func := by
  have hmem : (Lambda.intGeFunc : WFLFunc CoreLParams).func ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨_, intGeFunc_mem, rfl⟩
  exact Lambda.Factory.get?_ofArray_of_mem hmem Core.WFFactoryArray_func_name_nodup

theorem callOfLFunc_intGe (a b : E) (aPA : Bool) :
    Core.Factory.callOfLFunc (intGe a b) (allowPartialApp := aPA)
      = some (.op () ⟨"Int.Ge", ()⟩ (some (.arrow .int (.arrow .int .bool))), [a, b],
          (Lambda.intGeFunc : WFLFunc CoreLParams).func) := by
  have hget : Core.Factory[("Int.Ge" : String)]? =
      some (Lambda.intGeFunc : WFLFunc CoreLParams).func := factory_get_intGe
  simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go, intGe, hget]
  cases aPA <;> simp [Lambda.intGeFunc, Lambda.binaryOp]

theorem isValue_intGe_false (a b : E) : LExpr.isValue Core.Factory (intGe a b) = false := by
  rw [LExpr.isValue.eq_def]
  split <;> (try (rename_i h; simp [intGe] at h))
  split
  · rename_i h
    rw [callOfLFunc_intGe] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    simp [Lambda.intGeFunc, Lambda.binaryOp]
  · rfl

theorem intGeFunc_attr : (Lambda.intGeFunc : WFLFunc CoreLParams).func.attr = #[] := by
  simp [Lambda.intGeFunc, Lambda.binaryOp]
theorem intGeFunc_body : (Lambda.intGeFunc : WFLFunc CoreLParams).func.body = none := by
  simp [Lambda.intGeFunc, Lambda.binaryOp]

theorem shortCircuitCall_intGe (args : List E) :
    LExpr.shortCircuitCall? (Lambda.intGeFunc : WFLFunc CoreLParams).func args = none := by
  unfold LExpr.shortCircuitCall?
  rw [intGeFunc_attr]
  rfl

/-- `Int.Ge` on two arguments that evaluate to integer literals in one step. -/
theorem eval_intGe_args (env : Lambda.Env CoreLParams) (a' b' : E) (a b : Int)
    (ha : LExpr.eval 1 Core.Factory env a' = (.intConst () a, .value true))
    (hb : LExpr.eval 1 Core.Factory env b' = (.intConst () b, .value true)) :
    LExpr.eval 2 Core.Factory env (intGe a' b') = (.boolConst () (decide (a ≥ b)), .value true) := by
  show LExpr.eval (Nat.succ 1) Core.Factory env _ = _
  rw [LExpr.eval.eq_2 (TBase := CoreLParams), isValue_intGe_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [callOfLFunc_intGe]
  dsimp only
  rw [shortCircuitCall_intGe]
  simp only [List.map_cons, List.map_nil, ha, hb, intGeFunc_body, intGeFunc_attr,
    Option.isSome_none, Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceDIte,
    attr_findInlineIfConstr_empty, attr_findEvalIfConstr_empty, attr_findEvalIfValue_empty,
    attr_hasInlineIfAllValues_empty, attr_contains_inline_empty,
    List.all_cons, List.all_nil, Lambda.isValue_const_true, Bool.and_true, Bool.true_and,
    Bool.true_or, Bool.or_false, ↓reduceIte, unit_metadata,
    Lambda.intGeFunc, Lambda.binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
    LExpr.denoteInt, LExpr.intConst, LExpr.boolConst,
    eval_const, LExpr.combineEvalResValueFlag_eq_pair,
    LExpr.EvalResult.isValueTrue, LExpr.EvalResult.combineValueFlag, Bool.and_self]

/-- The lifting lemma the `if` rule needs: `x >= y` in a store binding `x` and `y` to
    integer literals evaluates to the Boolean literal `a ≥ b`. -/
theorem evalFully_intGe_store (env : Lambda.Env CoreLParams) (x y : Core.Expression.Ident)
    (tx ty : Option LMonoTy) (a b : Int)
    (hx : env x = some (.intConst () a)) (hy : env y = some (.intConst () b)) :
    LExpr.evalFully Core.Factory env (intGe (.fvar () x tx) (.fvar () y ty))
      = some (.boolConst () (decide (a ≥ b))) :=
  Lambda.evalFully_of_value_true Core.Factory env _ 2 _
    (eval_intGe_args env _ _ a b
      (eval_fvar_value env x tx _ hx (isValue_intConst a))
      (eval_fvar_value env y ty _ hy (isValue_intConst b)))

/-! ## `Int.Ge` under any consistent model

The denotation half of the lifting: in every `Lambda.Interp Core.Factory`, the operator
applied to two integer literals denotes the Boolean the evaluator computes, because the
model agrees with the operator's concrete evaluation. -/

theorem intGe_mem_factory : "Int.Ge" ∈ Core.Factory :=
  Lambda.Factory.getElem?_some_implies_mem factory_get_intGe

theorem factory_getElem_intGe :
    Core.Factory["Int.Ge"]'intGe_mem_factory = (Lambda.intGeFunc : WFLFunc CoreLParams).func :=
  Lambda.Factory.getElem?_some_getElem factory_get_intGe

/-- `denote_intConst` with the type spelled as the lowering annotates it. -/
theorem denote_intConst' (tcInterp : TyConstrInterp) (opInterp : OpInterp tcInterp)
    (fv : FreeVarVal CoreLParams tcInterp) (vt : TyVarVal) {m : Unit} {i : Int}
    (h : LExpr.HasTypeA [] (LExpr.intConst m i : E) LMonoTy.int) :
    LExpr.denote tcInterp opInterp fv vt .nil (LExpr.intConst m i) LMonoTy.int h = i :=
  denote_intConst tcInterp opInterp fv vt .nil h

theorem hasTypeA_intGe_consts (c a : Int) :
    LExpr.HasTypeA [] (intGe (.intConst () c) (.intConst () a)) .bool :=
  .app (.app .op .const) .const

theorem denote_intGe_consts (I : Lambda.Interp Core.Factory)
    (fv : FreeVarVal CoreLParams I.tcInterp) (vt : TyVarVal) (c a : Int)
    (h : LExpr.HasTypeA [] (intGe (.intConst () c) (.intConst () a)) .bool) :
    LExpr.denote I.tcInterp I.opInterp fv vt .nil (intGe (.intConst () c) (.intConst () a)) .bool h
      = decide (c ≥ a) := by
  have hic := I.interpConsistent
  unfold Lambda.Factory.InterpConsistent at hic
  have hcons := hic.2 "Int.Ge" intGe_mem_factory
  rw [factory_getElem_intGe] at hcons
  cases hce : (Lambda.intGeFunc : WFLFunc CoreLParams).func.concreteEval with
  | none => simp [Lambda.intGeFunc, Lambda.binaryOp] at hce
  | some ceval =>
    have happ : ceval () [.intConst () c, .intConst () a] = some (.boolConst () (decide (c ≥ a))) := by
      simp [Lambda.intGeFunc, Lambda.binaryOp] at hce
      subst hce
      simp [LambdaLeanType.cevalTy, LambdaLeanType.mkConst, LExpr.denoteInt, LExpr.boolConst]
    have hspec := hcons ceval hce vt fv () Subst.empty [.intConst () c, .intConst () a]
      (.boolConst () (decide (c ≥ a))) happ
    have hs := hspec (.cons .const (.cons .const .nil)) .const
    have hc : LExpr.HasTypeA [] (LExpr.intConst () c : E) (.tcons "int" []) := .const
    have ha : LExpr.HasTypeA [] (LExpr.intConst () a : E) (.tcons "int" []) := .const
    have hop : LExpr.HasTypeA []
        (LExpr.op () ⟨"Int.Ge", ()⟩ (some (.arrow .int (.arrow .int .bool))) : E)
        (.arrow .int (.arrow .int .bool)) := .op
    have hfn : LExpr.HasTypeA []
        (LExpr.app () (LExpr.op () ⟨"Int.Ge", ()⟩ (some (.arrow .int (.arrow .int .bool))))
          (LExpr.intConst () c) : E) (.arrow .int .bool) := .app hop hc
    revert h
    unfold intGe
    intro h
    rw [denote_app (h_fn := hfn) (h_arg := ha), denote_app (h_fn := hop) (h_arg := hc),
      denote_op]
    first
    | exact hs.symm
    | (simp only [denote_intConst'] ; exact hs.symm)

/-! ## `Bool.And`, `Bool.Or` and `==` on literals, under any consistent model -/

set_option maxRecDepth 4000 in
theorem boolAndFunc_mem : (Lambda.boolAndFunc : WFLFunc CoreLParams) ∈ Core.WFFactoryArray := by
  rw [Array.mem_def]
  unfold Core.WFFactoryArray
  simp only [Array.toList_appendList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, true_or, or_true]

set_option maxRecDepth 4000 in
theorem boolOrFunc_mem : (Lambda.boolOrFunc : WFLFunc CoreLParams) ∈ Core.WFFactoryArray := by
  rw [Array.mem_def]
  unfold Core.WFFactoryArray
  simp only [Array.toList_appendList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, true_or, or_true]

theorem factory_get_of_mem (wf : WFLFunc CoreLParams) (h : wf ∈ Core.WFFactoryArray) :
    Core.Factory.get? wf.func.name.name = some wf.func :=
  Lambda.Factory.get?_ofArray_of_mem (Array.mem_map.mpr ⟨_, h, rfl⟩)
    Core.WFFactoryArray_func_name_nodup

theorem factory_get_boolAnd :
    Core.Factory.get? "Bool.And" = some (Lambda.boolAndFunc : WFLFunc CoreLParams).func :=
  factory_get_of_mem _ boolAndFunc_mem
theorem factory_get_boolOr :
    Core.Factory.get? "Bool.Or" = some (Lambda.boolOrFunc : WFLFunc CoreLParams).func :=
  factory_get_of_mem _ boolOrFunc_mem

/-- The denotation of a short-circuit Boolean operator on two Boolean literals: the
    model agrees with the operator's concrete evaluation, which decides the result from
    the first literal or returns the second. Shared by `Bool.And` and `Bool.Or`. -/
theorem denote_shortCircuit_consts (I : Lambda.Interp Core.Factory)
    (fv : FreeVarVal CoreLParams I.tcInterp) (vt : TyVarVal)
    (name : String) (absorb decided : Bool)
    (hget : Core.Factory.get? name
      = some (Lambda.shortCircuitOp (T := CoreLParams) ⟨name, ()⟩ absorb decided).func)
    (p q : Bool)
    (h : LExpr.HasTypeA []
      (.app () (.app () (.op () ⟨name, ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
        (.boolConst () p)) (.boolConst () q) : E) .bool) :
    LExpr.denote I.tcInterp I.opInterp fv vt .nil
      (.app () (.app () (.op () ⟨name, ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
        (.boolConst () p)) (.boolConst () q)) .bool h
      = (if p == absorb then decided else q) := by
  have hmem : name ∈ Core.Factory := Lambda.Factory.getElem?_some_implies_mem hget
  have hic := I.interpConsistent
  unfold Lambda.Factory.InterpConsistent at hic
  have hcons := hic.2 name hmem
  rw [Lambda.Factory.getElem?_some_getElem hget] at hcons
  cases hceq : (Lambda.shortCircuitOp (T := CoreLParams) ⟨name, ()⟩ absorb decided).func.concreteEval with
  | none => simp [Lambda.shortCircuitOp] at hceq
  | some ceval =>
    have happ : ceval () [.boolConst () p, .boolConst () q]
        = some (.boolConst () (if p == absorb then decided else q)) := by
      simp [Lambda.shortCircuitOp] at hceq
      subst hceq
      cases p <;> cases absorb <;>
        simp [LambdaLeanType.cevalTy, LambdaLeanType.mkConst, LExpr.denoteBool, LExpr.boolConst]
    have hspec := hcons ceval hceq vt fv () Subst.empty [.boolConst () p, .boolConst () q]
      (.boolConst () (if p == absorb then decided else q)) happ
    have hs := hspec (.cons .const (.cons .const .nil)) .const
    have hp : LExpr.HasTypeA [] (LExpr.boolConst () p : E) (.tcons "bool" []) := .const
    have hq : LExpr.HasTypeA [] (LExpr.boolConst () q : E) (.tcons "bool" []) := .const
    have hop : LExpr.HasTypeA []
        (LExpr.op () ⟨name, ()⟩ (some (.arrow .bool (.arrow .bool .bool))) : E)
        (.arrow .bool (.arrow .bool .bool)) := .op
    have hfn : LExpr.HasTypeA []
        (LExpr.app () (LExpr.op () ⟨name, ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
          (LExpr.boolConst () p) : E) (.arrow .bool .bool) := .app hop hp
    rw [denote_app (h_fn := hfn) (h_arg := hq), denote_app (h_fn := hop) (h_arg := hp),
      denote_op]
    exact hs.symm

theorem denote_boolAnd_consts (I : Lambda.Interp Core.Factory)
    (fv : FreeVarVal CoreLParams I.tcInterp) (vt : TyVarVal) (p q : Bool)
    (h : LExpr.HasTypeA []
      (.app () (.app () (.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
        (.boolConst () p)) (.boolConst () q) : E) .bool) :
    LExpr.denote I.tcInterp I.opInterp fv vt .nil
      (.app () (.app () (.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
        (.boolConst () p)) (.boolConst () q)) .bool h = (p && q) := by
  rw [denote_shortCircuit_consts I fv vt "Bool.And" false false factory_get_boolAnd p q h]
  cases p <;> (try simp) <;> (try rfl)

theorem denote_boolOr_consts (I : Lambda.Interp Core.Factory)
    (fv : FreeVarVal CoreLParams I.tcInterp) (vt : TyVarVal) (p q : Bool)
    (h : LExpr.HasTypeA []
      (.app () (.app () (.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
        (.boolConst () p)) (.boolConst () q) : E) .bool) :
    LExpr.denote I.tcInterp I.opInterp fv vt .nil
      (.app () (.app () (.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
        (.boolConst () p)) (.boolConst () q)) .bool h = (p || q) := by
  rw [denote_shortCircuit_consts I fv vt "Bool.Or" true true factory_get_boolOr p q h]
  cases p <;> (try simp) <;> (try rfl)

/-- `Bool.And` on any two Boolean expressions: the operator denotes `&&`. The literal case
    carries the model fact; the general case follows because the denotation of a literal
    is, definitionally, its value. -/
theorem denote_boolAnd (I : Lambda.Interp Core.Factory)
    (fv : FreeVarVal CoreLParams I.tcInterp) (vt : TyVarVal) (e1 e2 : E)
    (h1 : LExpr.HasTypeA [] e1 .bool) (h2 : LExpr.HasTypeA [] e2 .bool)
    (h : LExpr.HasTypeA []
      (.app () (.app () (.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) e1) e2)
      .bool) :
    LExpr.denote I.tcInterp I.opInterp fv vt .nil
      (.app () (.app () (.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) e1) e2)
      .bool h
      = (LExpr.denote I.tcInterp I.opInterp fv vt .nil e1 .bool h1 &&
         LExpr.denote I.tcInterp I.opInterp fv vt .nil e2 .bool h2) := by
  have hop : LExpr.HasTypeA []
      (LExpr.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool))) : E)
      (.arrow .bool (.arrow .bool .bool)) := .op
  have hfn : LExpr.HasTypeA []
      (LExpr.app () (LExpr.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) e1 : E)
      (.arrow .bool .bool) := .app hop h1
  have hp : LExpr.HasTypeA []
      (LExpr.boolConst () (LExpr.denote I.tcInterp I.opInterp fv vt .nil e1 .bool h1) : E)
      (.tcons "bool" []) := .const
  have hq : LExpr.HasTypeA []
      (LExpr.boolConst () (LExpr.denote I.tcInterp I.opInterp fv vt .nil e2 .bool h2) : E)
      (.tcons "bool" []) := .const
  have hfnL : LExpr.HasTypeA []
      (LExpr.app () (LExpr.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
        (LExpr.boolConst () (LExpr.denote I.tcInterp I.opInterp fv vt .nil e1 .bool h1)) : E)
      (.arrow .bool .bool) := .app hop hp
  have hlit := denote_boolAnd_consts I fv vt
    (LExpr.denote I.tcInterp I.opInterp fv vt .nil e1 .bool h1)
    (LExpr.denote I.tcInterp I.opInterp fv vt .nil e2 .bool h2) (.app hfnL hq)
  rw [denote_app (h_fn := hfnL) (h_arg := hq), denote_app (h_fn := hop) (h_arg := hp),
    denote_op] at hlit
  rw [denote_app (h_fn := hfn) (h_arg := h2), denote_app (h_fn := hop) (h_arg := h1), denote_op]
  exact hlit

theorem denote_boolOr (I : Lambda.Interp Core.Factory)
    (fv : FreeVarVal CoreLParams I.tcInterp) (vt : TyVarVal) (e1 e2 : E)
    (h1 : LExpr.HasTypeA [] e1 .bool) (h2 : LExpr.HasTypeA [] e2 .bool)
    (h : LExpr.HasTypeA []
      (.app () (.app () (.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) e1) e2)
      .bool) :
    LExpr.denote I.tcInterp I.opInterp fv vt .nil
      (.app () (.app () (.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) e1) e2)
      .bool h
      = (LExpr.denote I.tcInterp I.opInterp fv vt .nil e1 .bool h1 ||
         LExpr.denote I.tcInterp I.opInterp fv vt .nil e2 .bool h2) := by
  have hop : LExpr.HasTypeA []
      (LExpr.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool))) : E)
      (.arrow .bool (.arrow .bool .bool)) := .op
  have hfn : LExpr.HasTypeA []
      (LExpr.app () (LExpr.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) e1 : E)
      (.arrow .bool .bool) := .app hop h1
  have hp : LExpr.HasTypeA []
      (LExpr.boolConst () (LExpr.denote I.tcInterp I.opInterp fv vt .nil e1 .bool h1) : E)
      (.tcons "bool" []) := .const
  have hq : LExpr.HasTypeA []
      (LExpr.boolConst () (LExpr.denote I.tcInterp I.opInterp fv vt .nil e2 .bool h2) : E)
      (.tcons "bool" []) := .const
  have hfnL : LExpr.HasTypeA []
      (LExpr.app () (LExpr.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool))))
        (LExpr.boolConst () (LExpr.denote I.tcInterp I.opInterp fv vt .nil e1 .bool h1)) : E)
      (.arrow .bool .bool) := .app hop hp
  have hlit := denote_boolOr_consts I fv vt
    (LExpr.denote I.tcInterp I.opInterp fv vt .nil e1 .bool h1)
    (LExpr.denote I.tcInterp I.opInterp fv vt .nil e2 .bool h2) (.app hfnL hq)
  rw [denote_app (h_fn := hfnL) (h_arg := hq), denote_app (h_fn := hop) (h_arg := hp),
    denote_op] at hlit
  rw [denote_app (h_fn := hfn) (h_arg := h2), denote_app (h_fn := hop) (h_arg := h1), denote_op]
  exact hlit

/-- `==` on two integer literals denotes their equality. -/
theorem denote_eq_ints (I : Lambda.Interp Core.Factory)
    (fv : FreeVarVal CoreLParams I.tcInterp) (vt : TyVarVal) (c a : Int)
    (h : LExpr.HasTypeA [] (.eq () (LExpr.intConst () c) (LExpr.intConst () a) : E) .bool) :
    LExpr.denote I.tcInterp I.opInterp fv vt .nil
      (.eq () (LExpr.intConst () c) (LExpr.intConst () a)) .bool h = decide (c = a) := by
  have hc : LExpr.HasTypeA [] (LExpr.intConst () c : E) LMonoTy.int := .const
  have ha : LExpr.HasTypeA [] (LExpr.intConst () a : E) LMonoTy.int := .const
  by_cases hca : c = a
  · subst hca
    rw [denote_eq_true _ hc ha h rfl]
    show (true : Bool) = decide (c = c)
    simp
  · rw [denote_eq_false _ hc ha h (by rw [denote_intConst', denote_intConst']; exact hca)]
    show (false : Bool) = decide (c = a)
    simp [hca]

end HoareLift


end -- public section
