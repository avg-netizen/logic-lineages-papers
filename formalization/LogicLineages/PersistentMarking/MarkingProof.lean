import LogicLineages.PersistentMarking.MarkingTargets

namespace LogicLineages.PersistentMarking.MarkingProof
open Term

theorem successAgrees (s t : Term) (h : mark s = some t) : headmark s = t := by
  cases s with
  | var σ x => simp [mark] at h
  | head f base => simpa [mark, headmark] using h
  | marked f τ base extras => simpa [mark, headmark] using h
  | lam σ x body =>
    cases hm : mark body with
    | none => simp [mark, hm] at h
    | some b =>
      have hb := successAgrees body b hm
      simp only [mark, hm, Option.map_some, Option.some.injEq] at h
      simpa [headmark, hb] using h
termination_by sizeOf s

theorem persistent (s t : Term) (h : mark s = some t) : mark t = some t := by
  cases s with
  | var σ x => simp [mark] at h
  | head f base =>
    simp only [mark, Option.some.injEq] at h
    subst t
    rfl
  | marked f τ base extras =>
    simp only [mark, Option.some.injEq] at h
    subst t
    rfl
  | lam σ x body =>
    cases hm : mark body with
    | none => simp [mark, hm] at h
    | some b =>
      have hb := persistent body b hm
      simp only [mark, hm, Option.map_some, Option.some.injEq] at h
      subst t
      simp [mark, hb]
termination_by sizeOf s

theorem totalIdempotent (s : Term) : headmark (headmark s) = headmark s := by
  cases s with
  | var σ x => rfl
  | head f base => rfl
  | marked f τ base extras => rfl
  | lam σ x body => simp only [headmark, totalIdempotent body]
termination_by sizeOf s

theorem failureExact (s : Term) : mark s = none ↔ variableSpine s = true := by
  cases s with
  | var σ x => simp [mark, variableSpine]
  | head f base => simp [mark, variableSpine]
  | marked f τ base extras => simp [mark, variableSpine]
  | lam σ x body =>
    cases hm : mark body with
    | none =>
      have hb := (failureExact body).mp hm
      simp [mark, variableSpine, hm, hb]
    | some b =>
      have hb : variableSpine body ≠ true := by
        intro h
        have hn := (failureExact body).mpr h
        simp [hm] at hn
      simp [mark, variableSpine, hm, hb]
termination_by sizeOf s

theorem typePreserved (s t : Term) (h : mark s = some t) : type t = type s := by
  cases s with
  | var σ x => simp [mark] at h
  | head f base =>
    simp only [mark, Option.some.injEq] at h
    subst t
    rfl
  | marked f τ base extras =>
    simp only [mark, Option.some.injEq] at h
    subst t
    rfl
  | lam σ x body =>
    cases hm : mark body with
    | none => simp [mark, hm] at h
    | some b =>
      have hb := typePreserved body b hm
      simp only [mark, hm, Option.map_some, Option.some.injEq] at h
      subst t
      simp [type, hb]
termination_by sizeOf s

theorem totalTypePreserved (s : Term) : type (headmark s) = type s := by
  cases s with
  | var σ x => rfl
  | head f base => rfl
  | marked f τ base extras => rfl
  | lam σ x body => simp only [headmark, type, totalTypePreserved body]
termination_by sizeOf s

end LogicLineages.PersistentMarking.MarkingProof
