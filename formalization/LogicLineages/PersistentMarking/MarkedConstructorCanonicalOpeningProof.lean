import LogicLineages.PersistentMarking.MarkedConstructorOpeningProof
import LogicLineages.PersistentMarking.ObservationLambdaProof

namespace LogicLineages.PersistentMarking.MarkedConstructorCanonicalOpeningProof
open Spine DecisionPorts ObservationLambda ProtectedSpineEnvironment

theorem firstUnusedMinimal (Γ : Context) (i : Nat) (hi : firstUnused Γ = some i) (j : Nat) (hj : j < i) :
    Γ[j]? ≠ some none := by
  induction Γ generalizing i j with
  | nil => cases hi
  | cons entry Γ ih =>
    cases entry with
    | none =>
      have hz : i = 0 := (Option.some.inj hi).symm
      omega
    | some σ =>
      cases hr : firstUnused Γ with
      | none => simp [firstUnused,hr] at hi
      | some k =>
        have he : k+1 = i := by simpa [firstUnused,hr] using hi
        subst i
        cases j with
        | zero => simp
        | succ j => exact ih k hr j (by omega)

theorem slotEq (Γ : Context) (i : Nat) (hi : firstUnused Γ = some i) : openingSlot Γ = some i := by
  have hnone := ObservationPortUpdateProof.firstSound Γ i hi
  obtain ⟨hib,_⟩ := List.getElem?_eq_some_iff.mp hnone
  unfold openingSlot
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp [hnone], i, by simpa using hib, by simp, ?_⟩
  intro j hj
  simp [firstUnusedMinimal Γ i hi j hj]

theorem fillAt (Γ : Context) (σ : Ty) (i j : Nat) :
    (fillSlot Γ i σ)[j]? = Γ[j]?.map (fun old => if j = i then some σ else old) := by
  induction Γ generalizing i j with
  | nil => cases i <;> cases j <;> rfl
  | cons entry Γ ih =>
    cases i <;> cases j <;> simp [fillSlot, ih]

theorem openingEqFill (Γ : Context) (σ : Ty) (i : Nat) :
    openingContext Γ σ i = fillSlot Γ i σ := by
  apply List.ext_getElem?
  intro j
  rw [MarkedConstructorOpeningProof.openingAt,fillAt]

end LogicLineages.PersistentMarking.MarkedConstructorCanonicalOpeningProof
