/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLift
import StrataBoole.MetaVerifier

/-! # `max2` against Core's Hoare logic, by hand

The first procedure proved on the Lean route of `docs/HoareLogic.md`. Everything the
tactic of step 1 will automate is written out once here; the lifting lemmas it uses
are in `StrataBoole.HoareLift`.
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

def intTy : Option LMonoTy := some (.tcons "int" [])
def xV : Core.Expression.Ident := ⟨"x", ()⟩
def yV : Core.Expression.Ident := ⟨"y", ()⟩
def rV : Core.Expression.Ident := ⟨"r", ()⟩

/-- Metadata of the statements, read off the program so the shapes below are exact. -/
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
      [.ite (.det (intGe (.fvar () xV intTy) (.fvar () yV intTy)))
        [.cmd (.cmd (.set rV (.det (.fvar () xV intTy)) md1))]
        [.cmd (.cmd (.set rV (.det (.fvar () yV intTy)) md2))] md3] md4] := by
  native_decide

/-! ## The contract as a triple -/

/-- Gate parameters: no reserved prefixes, every operator counts as declared. -/
def params : Core.Logic.InitEnvWFParams := ⟨[], fun _ => true⟩

theorem max2_checksTyped : Core.Logic.Hoare.Procedure.contractChecksTyped max2Proc := by
  native_decide

theorem max2_inputs : max2Proc.header.inputs.toList = [(xV, .tcons "int" []), (yV, .tcons "int" [])] := by
  native_decide

/-- `Bool.And a b` and `Bool.Or a b` as the lowering writes `a && b` and `a || b`. -/
abbrev andE (a b : E) : E :=
  .app () (.app () (.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) a) b
abbrev orE (a b : E) : E :=
  .app () (.app () (.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) a) b

/-- The clause labels carry source offsets, so they are read off the program too. -/
def lbl0 : Core.CoreLabel :=
  match max2Proc.spec.postconditions.toList with | (l, _) :: _ => l | _ => ""
def lbl1 : Core.CoreLabel :=
  match max2Proc.spec.postconditions.toList with | _ :: (l, _) :: _ => l | _ => ""

def mdP0 : Imperative.MetaData Core.Expression :=
  match max2Proc.spec.postconditions.toList with | (_, c) :: _ => c.md | _ => #[]
def mdP1 : Imperative.MetaData Core.Expression :=
  match max2Proc.spec.postconditions.toList with | _ :: (_, c) :: _ => c.md | _ => #[]

theorem max2_posts : max2Proc.spec.postconditions.toList =
    [(lbl0,
      { expr := andE (intGe (.fvar () rV intTy) (.fvar () xV intTy))
                     (intGe (.fvar () rV intTy) (.fvar () yV intTy)),
        attr := .Default, md := mdP0 }),
     (lbl1,
      { expr := orE (.eq () (.fvar () rV intTy) (.fvar () xV intTy))
                    (.eq () (.fvar () rV intTy) (.fvar () yV intTy)),
        attr := .Default, md := mdP1 })] := by
  native_decide

/-- A clause holds in every world once its captured form is a closed expression that
    denotes `true` under every valuation. -/
theorem check_of_captured (model : Lambda.Interp Core.Factory)
    (ρ : Imperative.Env Core.Expression) (label : Core.CoreLabel) (check : Core.Procedure.Check)
    (e : E) (hfac : ρ.factory = Core.Factory)
    (hcap : Core.Logic.capturedExpr
      { factory := ρ.factory, store := ρ.store, label := label,
        expr := check.expr, metadata := check.md } = e)
    (ht : LExpr.HasTypeA [] e .bool)
    (hd : ∀ (fv : FreeVarVal CoreLParams model.tcInterp) (vt : TyVarVal),
      LExpr.denote model.tcInterp model.opInterp fv vt .nil e .bool ht = true) :
    Core.Logic.Hoare.Procedure.checkAsPredicate model ρ label check := by
  intro world
  refine Or.inl ⟨hfac, ?_⟩
  rw [hcap]
  exact ⟨ht, hd _ _⟩

/-- The two `ensures` clauses, read in every world of `model`, once the store binds the
    three variables to integer literals satisfying them. -/
theorem max2_post (model : Lambda.Interp Core.Factory) (ρ : Imperative.Env Core.Expression)
    (a b c : Int) (hfac : ρ.factory = Core.Factory)
    (hx : ρ.store xV = some (.intConst () a)) (hy : ρ.store yV = some (.intConst () b))
    (hr : ρ.store rV = some (.intConst () c))
    (h1 : c ≥ a) (h2 : c ≥ b) (h3 : c = a ∨ c = b) :
    Core.Logic.Hoare.Procedure.contractPost model max2Proc ρ := by
  intro label check hmem _
  rw [max2_posts] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  have hc : LExpr.HasTypeA [] (LExpr.intConst () c : E) LMonoTy.int := .const
  have ha : LExpr.HasTypeA [] (LExpr.intConst () a : E) LMonoTy.int := .const
  have hb : LExpr.HasTypeA [] (LExpr.intConst () b : E) LMonoTy.int := .const
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine check_of_captured model ρ _ _
      (andE (intGe (.intConst () c) (.intConst () a)) (intGe (.intConst () c) (.intConst () b)))
      hfac ?_ (.app (.app .op (hasTypeA_intGe_consts c a)) (hasTypeA_intGe_consts c b)) ?_
    · simp [Core.Logic.capturedExpr, LExpr.substFvarsFromEnv, Lambda.Env.mk, hx, hy, hr, intGe]
    · intro fv vt
      rw [denote_boolAnd _ _ _ _ _ (hasTypeA_intGe_consts c a) (hasTypeA_intGe_consts c b),
        denote_intGe_consts, denote_intGe_consts]
      show (decide (c ≥ a) && decide (c ≥ b)) = true
      simp [h1, h2]
  · refine check_of_captured model ρ _ _
      (orE (.eq () (.intConst () c) (.intConst () a)) (.eq () (.intConst () c) (.intConst () b)))
      hfac ?_ (.app (.app .op (.eq hc ha)) (.eq hc hb)) ?_
    · simp [Core.Logic.capturedExpr, LExpr.substFvarsFromEnv, Lambda.Env.mk, hx, hy, hr]
    · intro fv vt
      rw [denote_boolOr _ _ _ _ _ (.eq hc ha) (.eq hc hb), denote_eq_ints, denote_eq_ints]
      show (decide (c = a) || decide (c = b)) = true
      rcases h3 with rfl | rfl <;> simp

/-- From `contractPre`: the inputs are integer literals. -/
theorem max2_pre_ints (model : Lambda.Interp Core.Factory) (ρ : Imperative.Env Core.Expression)
    (hpre : Core.Logic.Hoare.Procedure.contractPre model max2Proc ρ) :
    ρ.factory = Core.Factory ∧
      ∃ a b : Int, ρ.store xV = some (.intConst () a) ∧ ρ.store yV = some (.intConst () b) := by
  obtain ⟨-, hfac, -, hin⟩ := hpre
  refine ⟨hfac, ?_⟩
  have hx := hin xV (.tcons "int" []) (by rw [max2_inputs]; simp)
  have hy := hin yV (.tcons "int" []) (by rw [max2_inputs]; simp)
  obtain ⟨vx, hvx, a, rfl⟩ := hx
  obtain ⟨vy, hvy, b, rfl⟩ := hy
  exact ⟨a, b, hvx, hvy⟩

/-- `Core.Logic.Hoare.set` where the right-hand side is a variable the store binds to an
    integer literal: the assigned value is that literal. -/
theorem set_int_var (π : String → Option Core.Procedure) (x src : Core.Expression.Ident)
    (ty : Option LMonoTy) (md : Imperative.MetaData Core.Expression)
    (Pre Post : Imperative.Env Core.Expression → Prop)
    (hsrc : ∀ ρ₀, Pre ρ₀ → ∃ a : Int, ρ₀.store src = some (.intConst () a))
    (hpost : ∀ (ρ₀ : Imperative.Env Core.Expression) (σ' : Core.CoreStore) (a : Int), Pre ρ₀ →
      ρ₀.store src = some (.intConst () a) →
      σ' x = some (.intConst () a) → (∀ w, x ≠ w → σ' w = ρ₀.store w) →
      Post { ρ₀ with store := σ' }) :
    Core.Logic.Hoare.Triple π params Pre [Core.Statement.set x (.fvar () src ty) md] Post :=
  Core.Logic.Hoare.set π params x _ md Pre Post
    (fun ρ₀ σ' v hpre hev hup => by
      obtain ⟨a, ha⟩ := hsrc ρ₀ hpre
      have hv : v = .intConst () a := (Option.some.injEq _ _).mp
        (hev.symm.trans (Lambda.evalFully_fvar_of_value ρ₀.factory ρ₀.store () src ty _ ha
          (Lambda.isValue_const_true _ _ _)))
      subst hv
      cases hup with
      | update _hold hnew hoth => exact hpost ρ₀ σ' a hpre ha hnew hoth)

theorem max2_triple : Core.Logic.Hoare.Procedure.contractTriple max2Core params "max2" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed max2Core params "max2" max2Proc _
    max2_findProc max2_body_eq max2_checksTyped (fun model => ?_)
  -- the procedure block, then the labelled block
  refine (Core.Logic.Hoare.block max2Core.findProcByString? params ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))) model
  refine Core.Logic.Hoare.block max2Core.findProcByString? params ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  -- the if: each branch is one assignment whose value we know
  refine Core.Logic.Hoare.ite max2Core.findProcByString? params ?_ ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  · -- then: r := x under x >= y
    refine set_int_var _ rV xV intTy md1 _ _ ?_ ?_
    · intro ρ₀ ⟨hpre, _⟩
      obtain ⟨_, a, b, hx, _⟩ := max2_pre_ints model ρ₀ hpre
      exact ⟨a, hx⟩
    · intro ρ₀ σ' a ⟨hpre, hcond⟩ hxa hnew hoth
      obtain ⟨hfac, a', b, hx, hy⟩ := max2_pre_ints model ρ₀ hpre
      rw [hx] at hxa; cases hxa
      have hge : b ≤ a := by
        rw [hfac, show Core.Expression.eval = Lambda.LExpr.evalFully (TBase := CoreLParams) from rfl,
          evalFully_intGe_store _ _ _ _ _ a b hx hy] at hcond
        have htt : (Imperative.HasBool.tt : E) = .const () (.boolConst true) := rfl
        simpa [htt, LExpr.boolConst] using hcond
      have hne : rV ≠ xV := by decide
      have hne' : rV ≠ yV := by decide
      exact max2_post model _ a b a hfac (by simpa [hoth _ hne] using hx)
        (by simpa [hoth _ hne'] using hy) hnew (Int.le_refl a) hge (Or.inl rfl)
  · -- else: r := y under ¬ (x >= y)
    refine set_int_var _ rV yV intTy md2 _ _ ?_ ?_
    · intro ρ₀ ⟨hpre, _⟩
      obtain ⟨_, a, b, _, hy⟩ := max2_pre_ints model ρ₀ hpre
      exact ⟨b, hy⟩
    · intro ρ₀ σ' b ⟨hpre, hcond⟩ hyb hnew hoth
      obtain ⟨hfac, a, b', hx, hy⟩ := max2_pre_ints model ρ₀ hpre
      rw [hy] at hyb; cases hyb
      have hlt : ¬ b ≤ a := by
        rw [hfac, show Core.Expression.eval = Lambda.LExpr.evalFully (TBase := CoreLParams) from rfl,
          evalFully_intGe_store _ _ _ _ _ a b hx hy] at hcond
        have hff : (Imperative.HasBool.ff : E) = .const () (.boolConst false) := rfl
        simpa [hff, LExpr.boolConst] using hcond
      have hne : rV ≠ xV := by decide
      have hne' : rV ≠ yV := by decide
      exact max2_post model _ a b b hfac (by simpa [hoth _ hne] using hx)
        (by simpa [hoth _ hne'] using hy) hnew (by omega) (Int.le_refl b) (Or.inr rfl)

end HoareMax2

