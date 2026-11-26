module

public import LogicLineages.NativeModule.PersistentMarking.SpineSubstitutionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.SpineCallTypingProof
open Spine

theorem consumeExact (Γ : BoundContext) (σ : Ty) (args : Args) (τ : Ty)
    (h : CallTyped Γ σ args τ) : consumeTypes σ args = some τ := by
  induction h with
  | nil => simp [consumeTypes]
  | cons hx hxs ih =>
    have ht := SpineShiftProof.annotationExact _ _ _ hx
    simp only [consumeTypes, ht]
    exact ih

theorem callExtras (Γ : BoundContext) (σ : Ty) (args : Args) (τ : Ty)
    (h : CallTyped Γ σ args τ) : ExtrasTyped Γ args := by
  induction h with
  | nil => exact .nil
  | cons hx hxs ih => exact .cons hx ih

theorem appendExtras (Γ : BoundContext) (left right : Args)
    (hl : ExtrasTyped Γ left) (hr : ExtrasTyped Γ right) :
    ExtrasTyped Γ (left.append right) := by
  cases left with
  | nil => exact hr
  | cons x xs =>
    cases hl with
    | cons hx hxs => exact .cons hx (appendExtras _ _ _ hxs hr)
termination_by sizeOf left

theorem auxPreserves (q : Expr) (args values : Args) (Γ : BoundContext)
    (types : List Ty) (σ τ : Ty) (r : Expr)
    (hv : BaseTyped Γ values types)
    (hq : Typed (BoundContext.«prefix» types Γ) q σ)
    (ha : CallTyped Γ σ args τ) (hr : applyAux q args values = some r) :
    Typed Γ r τ := by
  cases args with
  | nil =>
    cases ha
    simp only [applyAux, Option.some.injEq] at hr
    subst r
    exact SpineSubstitutionProof.parallelPreserves _ _ _ _ _ hv hq
  | cons a rest =>
    cases q with
    | free δ x => simp [applyAux] at hr
    | bound δ i => simp [applyAux] at hr
    | lam δ body =>
      cases hq with
      | lam hb =>
        cases ha with
        | cons harg hrest =>
          have hann := SpineShiftProof.annotationExact _ _ _ harg
          have hres : applyAux body rest (.cons a values) = some r := by
            simpa [applyAux, hann] using hr
          exact auxPreserves body rest (.cons a values) Γ _ _ _ r
            (.cons harg hv) hb hrest hres
    | head f base =>
      cases hq with
      | head hb =>
        have hc := consumeExact _ _ _ _ ha
        simp only [applyAux, hc, Option.map_some, Option.some.injEq] at hr
        subst r
        exact .marked (SpineSubstitutionProof.parallelBasePreserves _ _ _ _ _ hv hb)
          (callExtras _ _ _ _ ha)
    | marked f δ base extras =>
      cases hq with
      | marked hb he =>
        have hc := consumeExact _ _ _ _ ha
        simp only [applyAux, hc, Option.map_some, Option.some.injEq] at hr
        subst r
        exact .marked (SpineSubstitutionProof.parallelBasePreserves _ _ _ _ _ hv hb)
          (appendExtras _ _ _
            (SpineSubstitutionProof.parallelExtrasPreserves _ _ _ _ hv he)
            (callExtras _ _ _ _ ha))
termination_by sizeOf args

theorem callPreserves : SpineTypingTargets.CallPreserves := by
  intro Γ q σ args τ r hq ha hr
  cases args with
  | nil =>
    cases ha
    simp only [apply, Option.some.injEq] at hr
    subst r
    exact hq
  | cons a rest =>
    exact auxPreserves q (.cons a rest) .nil Γ [] σ τ r .nil hq ha hr
end LogicLineages.PersistentMarking.SpineCallTypingProof
