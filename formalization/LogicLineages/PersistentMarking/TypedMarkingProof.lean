import LogicLineages.PersistentMarking.TypedMarkingTargets

namespace LogicLineages.PersistentMarking.TypedMarkingProof
open Term

theorem annotationExact (Γ : Context) (s : Term) (σ : Ty) (h : Typed Γ s σ) :
    s.type = σ := by
  cases h with
  | var _ => rfl
  | head _ => rfl
  | marked _ _ => rfl
  | lam hb =>
    simp only [Term.type, annotationExact _ _ _ hb]
termination_by sizeOf s

theorem partialPreserves (Γ : Context) (s : Term) (σ : Ty) (h : Typed Γ s σ)
    (t : Term) (hm : s.mark = some t) : Typed Γ t σ := by
  cases s with
  | var δ x => simp [mark] at hm
  | head f base =>
    cases h with
    | head hb =>
      simp only [mark, Option.some.injEq] at hm
      subst t
      exact .marked hb .nil
  | marked f δ base extras =>
    cases h with
    | marked hb he =>
      simp only [mark, Option.some.injEq] at hm
      subst t
      exact .marked hb he
  | lam δ x body =>
    cases h with
    | lam hb =>
      cases hx : mark body with
      | none => simp [mark, hx] at hm
      | some b =>
        have ht := partialPreserves _ _ _ hb b hx
        simp only [mark, hx, Option.map_some, Option.some.injEq] at hm
        subst t
        exact .lam ht
termination_by sizeOf s

theorem totalPreserves (Γ : Context) (s : Term) (σ : Ty) (h : Typed Γ s σ) :
    Typed Γ s.headmark σ := by
  cases h with
  | var hv => exact .var hv
  | head hb => exact .marked hb .nil
  | marked hb he => exact .marked hb he
  | lam hb => exact .lam (totalPreserves _ _ _ hb)
termination_by sizeOf s

end LogicLineages.PersistentMarking.TypedMarkingProof
