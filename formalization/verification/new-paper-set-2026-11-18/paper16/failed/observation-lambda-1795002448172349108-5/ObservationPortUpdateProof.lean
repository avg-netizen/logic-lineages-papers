import LogicLineages.PersistentMarking.ObservationLambdaTargets
import LogicLineages.PersistentMarking.DecisionPortsProof
namespace LogicLineages.PersistentMarking.ObservationPortUpdateProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations ObservationLambda

theorem firstSound (Γ : Context) (i : Nat) (h : firstUnused Γ = some i) : Γ[i]? = some none := by
  induction Γ generalizing i with
  | nil => cases h
  | cons entry rest ih =>
    cases entry with
    | none => simp only [firstUnused,Option.some.injEq] at h; subst i; rfl
    | some σ =>
      cases hr : firstUnused rest with
      | none => simp [firstUnused,hr] at h
      | some j =>
        simp only [firstUnused,hr,Option.map_some,Option.some.injEq] at h
        subst i; exact ih j hr

theorem firstComplete (Γ : Context) (h : used Γ < Γ.length) : ∃ i, firstUnused Γ = some i := by
  induction Γ with
  | nil => simp [used] at h
  | cons entry rest ih =>
    cases entry with
    | none => exact ⟨0,rfl⟩
    | some σ =>
      have hh : used rest < rest.length := by simp only [used,List.length_cons] at h; omega
      obtain ⟨i,hi⟩ := ih hh
      exact ⟨i+1,by simp only [firstUnused,hi,Option.map_some]⟩

theorem fillExact (Γ : Context) (i : Nat) (σ : Ty) (h : Γ[i]? = some none) :
    (fillSlot Γ i σ).length = Γ.length ∧ Extends Γ (fillSlot Γ i σ) ∧
    (fillSlot Γ i σ)[i]? = some (some σ) ∧ used (fillSlot Γ i σ) = used Γ + 1 := by
  induction Γ generalizing i with
  | nil => cases i <;> cases h
  | cons entry rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at h
      subst entry
      refine ⟨rfl,⟨rfl,?_⟩,rfl,?_⟩
      · intro j τ hj; cases j with
        | zero => simp at hj
        | succ j => exact hj
      · simp only [fillSlot,used]; omega
    | succ i =>
      obtain ⟨hl,he,hi,hc⟩ := ih i h
      refine ⟨by simp only [fillSlot,List.length_cons,hl],⟨by simp only [fillSlot,List.length_cons,hl],?_⟩,hi,?_⟩
      · intro j τ hj; cases j with
        | zero => exact hj
        | succ j => exact he.2 j τ hj
      · cases entry <;> simp only [fillSlot,used,hc] <;> omega

theorem fillWellFormed (K : List Ty) (B : Nat) (Γ : Context) (i : Nat) (σ : Ty)
    (hw : WellFormed K B Γ) (hi : Γ[i]? = some none) (hs : σ ∈ K) : WellFormed K B (fillSlot Γ i σ) := by
  have all : ∀ (Γ : Context) (i : Nat), (∀ (j : Nat) (τ : Ty), Γ[j]? = some (some τ) → τ ∈ K) →
      ∀ (j : Nat) (τ : Ty), (fillSlot Γ i σ)[j]? = some (some τ) → τ ∈ K := by
    intro Γ
    induction Γ with
    | nil => intro i h j τ hj; cases i <;> cases j <;> cases hj
    | cons entry rest ih =>
      intro i h j τ hj
      cases i with
      | zero => cases j with
        | zero => simp only [fillSlot,List.getElem?_cons_zero,Option.some.injEq] at hj; subst τ; exact hs
        | succ j => exact h (j+1) τ hj
      | succ i => cases j with
        | zero => exact h 0 τ hj
        | succ j => exact ih i (fun k υ hk => h (k+1) υ hk) j τ hj
  exact ⟨(fillExact Γ i σ hi).1.trans hw.1,all Γ i hw.2⟩

theorem assignmentWeakening (V : List Name) (Γ Δ : Context) (stack : List Ty) (vs : Args)
    (he : Extends Γ Δ) (h : Assignment V Γ stack vs) : Assignment V Δ stack vs := by
  induction h with
  | nil => exact .nil
  | cons hq hqs ih =>
    obtain ⟨i,hi,hq⟩ := hq
    exact .cons ⟨i,he.2 i _ hi,hq⟩ ih

theorem assignmentPrepend (V : List Name) (Γ : Context) (stack : List Ty) (vs : Args) (i : Nat) (σ : Ty)
    (h : Assignment V Γ stack vs) (hi : Γ[i]? = some none) :
    Assignment V (fillSlot Γ i σ) (σ::stack) (.cons (.free σ (portName V i)) vs) :=
  .cons ⟨i,(fillExact Γ i σ hi).2.2.1,rfl⟩
    (assignmentWeakening V Γ (fillSlot Γ i σ) stack vs (fillExact Γ i σ hi).2.1 h)
end LogicLineages.PersistentMarking.ObservationPortUpdateProof
