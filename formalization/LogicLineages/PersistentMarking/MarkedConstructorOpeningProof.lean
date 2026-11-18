import LogicLineages.PersistentMarking.MarkedConstructorTargets

namespace LogicLineages.PersistentMarking.MarkedConstructorOpeningProof
open Spine DecisionPorts ProtectedSpineEnvironment

theorem slotUnused (Γ : Context) (i : Nat) (hi : openingSlot Γ = some i) :
    Γ[i]? = some none := by
  have h : (fun j => decide (Γ[j]? = some none)) i = true :=
    List.find?_some (p := fun j => decide (Γ[j]? = some none)) hi
  exact decide_eq_true_eq.mp h

theorem openingAt (Γ : Context) (σ : Ty) (i j : Nat) :
    (openingContext Γ σ i)[j]? = Γ[j]?.map (fun old => if j = i then some σ else old) := by
  simp [openingContext, Function.comp_def]

theorem openingWellFormed (K : List Ty) (B : Nat) (Γ : Context) (σ : Ty) (i : Nat)
    (hw : WellFormed K B Γ) (hσ : σ ∈ K) (hi : Γ[i]? = some none) :
    WellFormed K B (openingContext Γ σ i) := by
  refine ⟨by simpa [openingContext] using hw.1,?_⟩
  intro j τ hj
  rw [openingAt] at hj
  by_cases he : j = i
  · subst j
    have h : σ = τ := by simpa [hi] using hj
    exact h ▸ hσ
  · exact hw.2 j τ (by simpa [he] using hj)

theorem openingExtends (Γ : Context) (σ : Ty) (i : Nat) (hi : Γ[i]? = some none) :
    Extends Γ (openingContext Γ σ i) := by
  refine ⟨by simp [openingContext],?_⟩
  intro j τ hj
  by_cases he : j = i
  · subst j
    rw [hi] at hj
    cases hj
  · simp [openingAt, hj, he]

end LogicLineages.PersistentMarking.MarkedConstructorOpeningProof
