import LogicLineages.PersistentMarking.DecisionPortsTargets
namespace LogicLineages.PersistentMarking.DecisionPortsProof
open Spine NameBridge DecisionPorts

theorem enumeration (K : List Ty) (B : Nat) (Γ : Context) : Γ ∈ contexts K B ↔ WellFormed K B Γ := by
  induction B generalizing Γ with
  | zero =>
    constructor
    · intro h; simp only [contexts,List.mem_singleton] at h; subst Γ
      exact ⟨rfl,by intro i σ h; cases i <;> simp at h⟩
    · rintro ⟨h,_⟩; have : Γ = [] := List.length_eq_zero.mp h
      subst Γ; simp [contexts]
  | succ B ih =>
    constructor
    · intro h
      obtain ⟨entry,he,hr⟩ := List.mem_flatMap.mp h
      obtain ⟨rest,hr,rfl⟩ := List.mem_map.mp hr
      have hw := (ih rest).mp hr
      refine ⟨by simp [hw.1], ?_⟩
      intro i σ hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
        subst entry
        simpa using he
      | succ i => exact hw.2 i σ hi
    · rintro ⟨hl,ht⟩
      cases Γ with
      | nil => simp at hl
      | cons entry rest =>
        have hr : WellFormed K B rest := ⟨by simpa using hl,fun i σ h => ht (i+1) σ h⟩
        have he : entry ∈ none :: K.map some := by
          cases entry with
          | none => simp
          | some σ => have hs := ht 0 σ rfl; simpa using hs
        exact List.mem_flatMap.mpr ⟨entry,he,List.mem_map.mpr ⟨rest,(ih rest).mpr hr,rfl⟩⟩

theorem extensionRefl (Γ : Context) : Extends Γ Γ := ⟨rfl,fun _ _ h => h⟩
theorem extensionTrans (Γ Δ Θ : Context) (h : Extends Γ Δ) (k : Extends Δ Θ) : Extends Γ Θ :=
  ⟨h.1.trans k.1,fun i σ hi => k.2 i σ (h.2 i σ hi)⟩

theorem usedBound (Γ : Context) : used Γ ≤ Γ.length := by
  induction Γ with
  | nil => exact Nat.le_refl _
  | cons entry rest ih => cases entry <;> simp only [used,List.length_cons] <;> omega

theorem usedMono (Γ Δ : Context) (h : Extends Γ Δ) : used Γ ≤ used Δ := by
  induction Γ generalizing Δ with
  | nil => exact Nat.zero_le _
  | cons entry rest ih =>
    cases Δ with
    | nil => have hh := h.1; simp at hh
    | cons entry' rest' =>
      have hr : Extends rest rest' := ⟨by simpa using h.1,fun i σ hi => h.2 (i+1) σ hi⟩
      have hh := ih rest' hr
      cases entry with
      | none => cases entry' <;> simp only [used] <;> omega
      | some σ =>
        have he := h.2 0 σ rfl
        simp only [List.getElem?_cons_zero,Option.some.injEq] at he
        subst entry'; simp only [used]; omega

theorem unused (Γ : Context) (h : used Γ < Γ.length) : ∃ (i : Nat), Γ[i]? = some none := by
  induction Γ with
  | nil => simp [used] at h
  | cons entry rest ih =>
    cases entry with
    | none => exact ⟨0,rfl⟩
    | some σ =>
      have hr : used rest < rest.length := by simpa only [used,List.length_cons] using h
      obtain ⟨i,hi⟩ := ih hr
      exact ⟨i+1,hi⟩

theorem nameBound (V : List Name) (σ : Ty) (x : Nat) (h : (σ,x) ∈ V) : x ≤ maxName V := by
  induction V with
  | nil => cases h
  | cons n ns ih =>
    rcases List.mem_cons.mp h with h|h
    · subst n; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
theorem fresh (V : List Name) (i : Nat) (σ : Ty) : (σ,portName V i) ∉ V := by
  intro h; have hb := nameBound V σ (portName V i) h
  simp only [portName] at hb; omega
theorem injective (V : List Name) (i j : Nat) (h : portName V i = portName V j) : i = j := by
  simp only [portName] at h; omega

theorem valuesExact (V : List Name) (Γ : Context) (σ : Ty) (q : Expr) : q ∈ values V Γ σ ↔ AtPort V Γ σ q := by
  simp only [values,List.mem_filterMap]
  constructor
  · rintro ⟨i,hi,hq⟩
    split at hq
    next h => exact ⟨i,h,(Option.some.inj hq).symm⟩
    next h => cases hq
  · rintro ⟨i,hi,rfl⟩
    obtain ⟨hb,_⟩ := List.getElem?_eq_some_iff.mp hi
    exact ⟨i,List.mem_range.mpr hb,by simp [hi]⟩
theorem valuesTyped (V : List Name) (Γ : Context) (σ : Ty) (q : Expr) (h : q ∈ values V Γ σ) : Typed EmptyContext q σ := by
  obtain ⟨i,_,rfl⟩ := (valuesExact V Γ σ q).mp h
  exact .free
theorem valuesWeaken (V : List Name) (Γ Δ : Context) (σ : Ty) (q : Expr) (he : Extends Γ Δ)
    (h : q ∈ values V Γ σ) : q ∈ values V Δ σ := by
  obtain ⟨i,hi,hq⟩ := (valuesExact V Γ σ q).mp h
  exact (valuesExact V Δ σ q).mpr ⟨i,he.2 i σ hi,hq⟩
end LogicLineages.PersistentMarking.DecisionPortsProof
