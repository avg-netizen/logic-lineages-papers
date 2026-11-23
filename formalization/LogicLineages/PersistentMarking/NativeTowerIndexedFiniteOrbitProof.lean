import LogicLineages.PersistentMarking.NativeIndexedCarrierFiniteOrbitProof
import LogicLineages.PersistentMarking.NativeTowerIndexedEntryProof
import LogicLineages.PersistentMarking.NativeOrdinalCapPathsTargets
import LogicLineages.PersistentMarking.StablePairProof

namespace LogicLineages.PersistentMarking.NativeTowerIndexedFiniteOrbitProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeIndexedCarrierSubtype
open NativeOrdinalBasisTargets NativeOrdinalBasisChecks NativeOrdinalArithmeticTargets
open NativeOrdinalCapPathsTargets NativeTowerIndexedEntryTargets NativeTowerIndexedEntryProof
open NativeTowerWitnessFamilyProof NativeIndexedCarrierFiniteOrbitProof

private theorem nativeRunStrict {S : Signature} {n : Nat}
    {source out : ClosedNativeTerm S indexType} (run : StrictRun S n source out) :
    n ≠ 0 → NativeBelow out source := by
  induction run with
  | nil => intro ne; exact False.elim (ne rfl)
  | @cons k s mid last raw actual tail ih =>
    intro _
    cases k with
    | zero =>
      cases tail
      exact actual
    | succ k =>
      exact StablePairProof.strictTransitive S s.val mid.val last.val actual (ih (Nat.succ_ne_zero k))

/-- The actual finite indices used below the exact original omega carrier. -/
def finiteIndex (S : Signature) (m : Nat) : ClosedNativeTerm S indexType :=
  finiteApplication (closedSuccessor S) (closedZero S) m

private theorem indexBelowOmega (S : Signature) (m : Nat) :
    NativeBelow (finiteIndex S m) (closedOmega S) := by
  have literal : cap (closedSuccessor S) (closedZero S) = closedOmega S := Subtype.ext rfl
  rw [← literal]
  exact (exact_CapAboveFiniteApplications S indexType (closedSuccessor S) (closedZero S) m).2

/-- The original tower witness dominates these exact finite approximants of
its own literal indexed entry. The inner map and seed are not parameters
supplied in place of the original source expressions. -/
theorem exact_ActualTowerIndexedFiniteOrbitDominance (S : Signature) (l : Nat) :
    ∃ (mapping : ClosedNativeTerm S endo) (seed : ClosedNativeTerm S indexType),
      mapping.val = innerMap l ∧ seed.val = successorSeed ∧
      StrictRun S (l+6) (closedTower S (l+2)) (indexedTerm .base mapping seed (closedOmega S)) ∧
      (∀ n, NativeBelow (finiteApplication mapping seed n) (closedTower S (l+2))) ∧
      (∀ (j : ClosedNativeTerm S indexType), NativeBelow j (closedOmega S) → ∀ n,
        NativeBelow (finiteApplication mapping (indexedTerm .base mapping seed j) n)
          (closedTower S (l+2))) ∧
      (∀ m n, NativeBelow
        (finiteApplication mapping (indexedTerm .base mapping seed (finiteIndex S m)) n)
        (closedTower S (l+2))) := by
  obtain ⟨mapping,seed,out,realMap,realSeed,realOut,run⟩ := exact_NativeTowerIndexedEntry S l
  let omegaTerm := indexedTerm .base mapping seed (closedOmega S)
  have outExact : out = omegaTerm := by
    apply Subtype.ext
    change out.val = indexedW .base mapping.val seed.val omegaCarrier
    rw [realMap,realSeed]
    exact realOut
  have path : StrictRun S (l+6) (closedTower S (l+2)) omegaTerm := by
    rw [← outExact]
    exact run
  have entryBelow : NativeBelow omegaTerm (closedTower S (l+2)) :=
    nativeRunStrict path (by omega)
  have earlier (j : ClosedNativeTerm S indexType) (less : NativeBelow j (closedOmega S)) (n : Nat) :
      NativeBelow (finiteApplication mapping (indexedTerm .base mapping seed j) n)
        (closedTower S (l+2)) :=
    StablePairProof.strictTransitive S _ _ _ entryBelow
      (exact_IndexedCarrierFiniteEarlierOrbit .base mapping seed (closedOmega S) j less n)
  refine ⟨mapping,seed,realMap,realSeed,path,?_,earlier,?_⟩
  · intro n
    exact StablePairProof.strictTransitive S _ _ _ entryBelow
      (exact_IndexedCarrierFiniteSeedOrbit .base mapping seed (closedOmega S) n)
  · intro m n
    exact earlier (finiteIndex S m) (indexBelowOmega S m) n

#print axioms exact_ActualTowerIndexedFiniteOrbitDominance

end LogicLineages.PersistentMarking.NativeTowerIndexedFiniteOrbitProof
