/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLift
import StrataBoole.MetaVerifier
import Strata.Languages.Core.ProgramProps

/-! # `max2` against Core's Hoare logic, by hand

The first procedure proved on the Lean route of `docs/HoareLogic.md`: a Boole block,
lowered to Core inside Lean, whose contract is proved by applying Core's Hoare rules.
Everything the tactic of step 1 will automate is written out once here. Expressions are
evaluated denotationally, so the values of variables are semantic values and the
evaluation lemmas of `Strata.Languages.Core.IntEvalProps` and `StrataBoole.HoareLift`
turn each rule's goal into a fact about integers.
-/

open Strata Lambda Core HoareLift

namespace HoareMax2

/-! ## The program -/

def max2Pgm : StrataDDM.Program :=
#strata
program Boole;
procedure max2 (x: int, y: int) returns (r: int)
spec {
  ensures r >= x && r >= y;
  ensures r == x || r == y;
}
{
  if (x >= y) { r := x; } else { r := y; }
};
#end

/-- The type-checked Core program the Boole block lowers to. -/
def max2Core : Core.Program :=
  match Strata.Boole.typeCheck max2Pgm with
  | .ok p => p
  | .error _ => default

def max2Proc : Core.Procedure := (max2Core.findProcByString? "max2").get!

theorem max2_findProc : max2Core.findProcByString? "max2" = some max2Proc := by native_decide

abbrev E := Core.Expression.Expr
def intTy : Option LMonoTy := some (.tcons "int" [])
def xV : Core.Expression.Ident := ⟨"x", ()⟩
def yV : Core.Expression.Ident := ⟨"y", ()⟩
def rV : Core.Expression.Ident := ⟨"r", ()⟩

/-- `a >= b`, `a && b`, `a || b` as the lowering writes them. -/
abbrev geE (a b : E) : E := .app () (.app () Core.intGeOp a) b
abbrev andE (a b : E) : E := .app () (.app () Core.boolAndOp a) b
abbrev orE (a b : E) : E := .app () (.app () Core.boolOrOp a) b

/-- The condition of the `if`. -/
abbrev cond : E := geE (.fvar () xV intTy) (.fvar () yV intTy)

/-- Metadata and labels of the statements and clauses, read off the program so the shapes
    below are exact. -/
def max2Body : Core.Statements :=
  match max2Proc.body with | .structured ss => ss | _ => []
def md4 : Imperative.MetaData Core.Expression :=
  match max2Body with | [.block _ _ md] => md | _ => #[]
def md3 : Imperative.MetaData Core.Expression :=
  match max2Body with | [.block _ [.ite _ _ _ md] _] => md | _ => #[]
def md1 : Imperative.MetaData Core.Expression :=
  match max2Body with | [.block _ [.ite _ [.cmd (.cmd (.set _ _ md))] _ _] _] => md | _ => #[]
def md2 : Imperative.MetaData Core.Expression :=
  match max2Body with | [.block _ [.ite _ _ [.cmd (.cmd (.set _ _ md))] _] _] => md | _ => #[]

theorem max2_body_eq : max2Proc.body = .structured
    [.block "max2"
      [.ite (.det cond)
        [.cmd (.cmd (.set rV (.det (.fvar () xV intTy)) md1))]
        [.cmd (.cmd (.set rV (.det (.fvar () yV intTy)) md2))] md3] md4] := by
  native_decide

def lbl0 : Core.CoreLabel :=
  match max2Proc.spec.postconditions.toList with | (l, _) :: _ => l | _ => ""
def lbl1 : Core.CoreLabel :=
  match max2Proc.spec.postconditions.toList with | _ :: (l, _) :: _ => l | _ => ""
def mdP0 : Imperative.MetaData Core.Expression :=
  match max2Proc.spec.postconditions.toList with | (_, c) :: _ => c.md | _ => #[]
def mdP1 : Imperative.MetaData Core.Expression :=
  match max2Proc.spec.postconditions.toList with | _ :: (_, c) :: _ => c.md | _ => #[]

theorem max2_posts : max2Proc.spec.postconditions.toList =
    [(lbl0, { expr := andE (geE (.fvar () rV intTy) (.fvar () xV intTy))
                            (geE (.fvar () rV intTy) (.fvar () yV intTy)),
              attr := .Default, md := mdP0 }),
     (lbl1, { expr := orE (.eq () (.fvar () rV intTy) (.fvar () xV intTy))
                          (.eq () (.fvar () rV intTy) (.fvar () yV intTy)),
              attr := .Default, md := mdP1 })] := by
  native_decide

theorem max2_inputs : max2Proc.header.inputs.toList =
    [(xV, .tcons "int" []), (yV, .tcons "int" [])] := by
  native_decide

theorem max2_checksTyped : Core.Logic.Hoare.Procedure.contractChecksTyped max2Proc := by
  native_decide

/-- No function precedes `max2`, so its visible factory is `Core.Factory`. -/
theorem max2_factory : max2Core.factoryBeforeProcedure "max2" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)

/-- Gate parameters: no reserved prefixes, every operator counts as declared. -/
def params : Core.Logic.InitEnvWFParams := ⟨[], fun _ => true⟩

/-! ## The values of the inputs -/

/-- An integer value of the environment's factory. -/
abbrev intV (f : Core.Expression.Factory) (n : Int) : Core.Expression.Val :=
  SemValue.ofInt f.model.tcInterp n

/-- Inside either branch the condition has evaluated, which binds `x` and `y` to values of
    the factory; with their declared type `int` they are integers. -/
theorem inputs_of_cond (ρ : Imperative.Env Core.Expression) {b : Bool}
    (hpre : Core.Logic.Hoare.Procedure.contractPre Core.Factory max2Proc ρ)
    (hcond : Core.Expression.eval ρ.factory ρ.store cond =
      some (SemValue.ofBool ρ.factory.model.tcInterp b)) :
    ρ.factory.factory = Core.Factory ∧
      ∃ a c : Int, ρ.store xV = some (intV ρ.factory a) ∧ ρ.store yV = some (intV ρ.factory c) := by
  obtain ⟨-, hfac, -, hin⟩ := hpre
  refine ⟨hfac, ?_⟩
  obtain ⟨vx, hx, hsx⟩ := hin xV (.tcons "int" []) (by rw [max2_inputs]; simp)
  obtain ⟨vy, hy, hsy⟩ := hin yV (.tcons "int" []) (by rw [max2_inputs]; simp)
  have hd := Lambda.LExpr.denoteEval_defines hcond
  have hvars : ∀ z ∈ [xV, yV], z ∈ Lambda.LExpr.LExpr.getVars cond := by
    simp [Lambda.LExpr.LExpr.getVars, Core.intGeOp, Lambda.WFLFunc.opExpr,
      Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr]
  obtain ⟨wx, hwx, htx⟩ := hd xV (hvars xV (by simp))
  obtain ⟨wy, hwy, hty⟩ := hd yV (hvars yV (by simp))
  rw [hx] at hwx; cases hwx
  rw [hy] at hwy; cases hwy
  obtain ⟨a, ha⟩ := Lambda.SemValue.exists_ofInt hsx
  obtain ⟨c, hc⟩ := Lambda.SemValue.exists_ofInt hsy
  rw [ha, htx] at hx
  rw [hc, hty] at hy
  exact ⟨a, c, hx, hy⟩

/-- The condition's Boolean, once the inputs are known. -/
theorem cond_eval (ρ : Imperative.Env Core.Expression) (a c : Int)
    (hfac : ρ.factory.factory = Core.Factory)
    (hx : ρ.store xV = some (intV ρ.factory a)) (hy : ρ.store yV = some (intV ρ.factory c)) :
    Core.Expression.eval ρ.factory ρ.store cond =
      some (SemValue.ofBool ρ.factory.model.tcInterp (decide (a ≥ c))) :=
  Core.eval_intGe (by rw [hfac]; exact Core.coreFactory_intGe)
    (Core.eval_fvar_int (ty := intTy) _ hx) (Core.eval_fvar_int (ty := intTy) _ hy)

/-! ## The postconditions -/

/-- The two `ensures` clauses hold in every world once the store binds `x`, `y` and `r` to
    integers satisfying them. -/
theorem max2_post (ρ : Imperative.Env Core.Expression) (a b c : Int)
    (hfac : ρ.factory.factory = Core.Factory)
    (hx : ρ.store xV = some (intV ρ.factory a)) (hy : ρ.store yV = some (intV ρ.factory b))
    (hr : ρ.store rV = some (intV ρ.factory c))
    (h1 : c ≥ a) (h2 : c ≥ b) (h3 : c = a ∨ c = b) :
    Core.Logic.Hoare.Procedure.contractPost Core.Factory max2Proc ρ := by
  intro label check hmem _
  rw [max2_posts] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  have er := Core.eval_fvar_int (ty := intTy) (m := ()) ρ.factory hx
  have ex := Core.eval_fvar_int (ty := intTy) (m := ()) ρ.factory hx
  have ey := Core.eval_fvar_int (ty := intTy) (m := ()) ρ.factory hy
  have err := Core.eval_fvar_int (ty := intTy) (m := ()) ρ.factory hr
  have hge : ρ.factory.factory["Int.Ge"]? = some (Lambda.intGeFunc (T := CoreLParams)).func := by
    rw [hfac]; exact Core.coreFactory_intGe
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> intro world <;> refine Or.inl ⟨hfac, ?_⟩ <;>
    show Core.Expression.eval ρ.factory ρ.store _ = some (Imperative.HasBool.ttVal ρ.factory)
  · rw [eval_boolAnd (by rw [hfac]; exact coreFactory_boolAnd)
      (Core.eval_intGe hge err ex) (Core.eval_intGe hge err ey)]
    simp [Imperative.HasBool.ttVal, h1, h2]
  · rw [eval_boolOr (by rw [hfac]; exact coreFactory_boolOr)
      (eval_eq_ints _ err ex) (eval_eq_ints _ err ey)]
    rcases h3 with rfl | rfl <;> simp [Imperative.HasBool.ttVal]

/-! ## The triple -/

theorem max2_triple : Core.Logic.Hoare.Procedure.contractTriple max2Core params "max2" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed max2Core params "max2" max2Proc _
    max2_findProc max2_body_eq max2_checksTyped ?_
  rw [max2_factory]
  -- the procedure block, then the labelled block
  refine Core.Logic.Hoare.block max2Core.findProcByString? params ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  refine Core.Logic.Hoare.block max2Core.findProcByString? params ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  -- the if: one assignment per branch
  refine Core.Logic.Hoare.ite max2Core.findProcByString? params ?_ ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  · -- then: r := x, under x >= y
    refine Core.Logic.Hoare.set max2Core.findProcByString? params rV _ md1 _ _ ?_
    intro ρ₀ σ' v ⟨hpre, hcond⟩ hev hup
    obtain ⟨hfac, a, c, hx, hy⟩ := inputs_of_cond ρ₀ hpre hcond
    have hge : a ≥ c := of_decide_eq_true (Lambda.SemValue.ofBool_injective
      (Option.some.inj ((cond_eval ρ₀ a c hfac hx hy).symm.trans hcond)))
    have hv : v = intV ρ₀.factory a :=
      Option.some.inj (hev.symm.trans (Core.eval_fvar_int (ty := intTy) _ hx))
    subst hv
    cases hup with
    | update _ hnew hoth =>
      exact max2_post { ρ₀ with store := σ' } a c a hfac
        ((hoth xV (by decide)).trans hx) ((hoth yV (by decide)).trans hy) hnew
        (Int.le_refl a) hge (Or.inl rfl)
  · -- else: r := y, under not (x >= y)
    refine Core.Logic.Hoare.set max2Core.findProcByString? params rV _ md2 _ _ ?_
    intro ρ₀ σ' v ⟨hpre, hcond⟩ hev hup
    obtain ⟨hfac, a, c, hx, hy⟩ := inputs_of_cond ρ₀ hpre hcond
    have hlt : ¬ a ≥ c := of_decide_eq_false (Lambda.SemValue.ofBool_injective
      (Option.some.inj ((cond_eval ρ₀ a c hfac hx hy).symm.trans hcond)))
    have hv : v = intV ρ₀.factory c :=
      Option.some.inj (hev.symm.trans (Core.eval_fvar_int (ty := intTy) _ hy))
    subst hv
    cases hup with
    | update _ hnew hoth =>
      exact max2_post { ρ₀ with store := σ' } a c c hfac
        ((hoth xV (by decide)).trans hx) ((hoth yV (by decide)).trans hy) hnew
        (by omega) (Int.le_refl c) (Or.inr rfl)

end HoareMax2
