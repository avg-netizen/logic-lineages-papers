import LogicLineages.PersistentMarking.SpineMarkingTargets
namespace LogicLineages.PersistentMarking.SpineMarkingProof
open Spine

theorem persistentSuccess (q r : Expr) (h : mark q = some r) : mark r = some r := by
  cases q with
  | free σ x => simp [mark] at h
  | bound σ i => simp [mark] at h
  | head f base => simp only [mark, Option.some.injEq] at h; subst r; rfl
  | marked f τ base extras => simp only [mark, Option.some.injEq] at h; subst r; rfl
  | lam σ body =>
    cases hm : mark body with
    | none => simp [mark, hm] at h
    | some b =>
      simp only [mark, hm, Option.map_some, Option.some.injEq] at h
      subst r
      simp only [mark, persistentSuccess body b hm, Option.map_some]
termination_by sizeOf q

theorem headmarkIdempotent (q : Expr) : headmark (headmark q) = headmark q := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | head f base => rfl
  | marked f τ base extras => rfl
  | lam σ body => simp only [headmark, headmarkIdempotent body]
termination_by sizeOf q

theorem markHeadmark (q r : Expr) (h : mark q = some r) : headmark q = r := by
  cases q with
  | free σ x => simp [mark] at h
  | bound σ i => simp [mark] at h
  | head f base => exact Option.some.inj h
  | marked f τ base extras => exact Option.some.inj h
  | lam σ body =>
    cases hm : mark body with
    | none => simp [mark, hm] at h
    | some b =>
      simp only [mark, hm, Option.map_some, Option.some.injEq] at h
      subst r
      simp only [headmark, markHeadmark body b hm]
termination_by sizeOf q

theorem markTyped (Γ : BoundContext) (q : Expr) (σ : Ty) (r : Expr)
    (hq : Typed Γ q σ) (hr : mark q = some r) : Typed Γ r σ := by
  cases q with
  | free δ x => simp [mark] at hr
  | bound δ i => simp [mark] at hr
  | head f base =>
    cases hq with
    | head hb =>
      simp only [mark, Option.some.injEq] at hr
      subst r
      exact .marked hb .nil
  | marked f τ base extras =>
    simp only [mark, Option.some.injEq] at hr
    subst r
    exact hq
  | lam δ body =>
    cases hq with
    | lam hb =>
      cases hm : mark body with
      | none => simp [mark, hm] at hr
      | some b =>
        simp only [mark, hm, Option.map_some, Option.some.injEq] at hr
        subst r
        exact .lam (markTyped _ body _ b hb hm)
termination_by sizeOf q

theorem headmarkTyped (Γ : BoundContext) (q : Expr) (σ : Ty)
    (hq : Typed Γ q σ) : Typed Γ (headmark q) σ := by
  cases q with
  | free δ x => exact hq
  | bound δ i => exact hq
  | head f base => cases hq with | head hb => exact .marked hb .nil
  | marked f τ base extras => exact hq
  | lam δ body => cases hq with | lam hb => exact .lam (headmarkTyped _ body _ hb)
termination_by sizeOf q

theorem covariance (θ : FreeMap) (d : Nat) (q r : Expr) (h : mark q = some r) :
    mark (freeSub θ d q) = some (freeSub θ d r) := by
  cases q with
  | free σ x => simp [mark] at h
  | bound σ i => simp [mark] at h
  | head f base => simp only [mark, Option.some.injEq] at h; subst r; rfl
  | marked f τ base extras => simp only [mark, Option.some.injEq] at h; subst r; rfl
  | lam σ body =>
    cases hm : mark body with
    | none => simp [mark, hm] at h
    | some b =>
      simp only [mark, hm, Option.map_some, Option.some.injEq] at h
      subst r
      simp only [freeSub, mark, covariance θ (d+1) body b hm, Option.map_some]
termination_by sizeOf q
end LogicLineages.PersistentMarking.SpineMarkingProof
