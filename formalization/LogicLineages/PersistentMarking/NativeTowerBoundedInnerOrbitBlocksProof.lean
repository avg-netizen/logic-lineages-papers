import LogicLineages.PersistentMarking.NativeIndexedCarrierOrbitBlocksProof
import LogicLineages.PersistentMarking.NativeTowerInnerMapHigherIteratorProof
import LogicLineages.PersistentMarking.NativeTowerIndexedFiniteOrbitProof

namespace LogicLineages.PersistentMarking.NativeTowerBoundedInnerOrbitBlocksProof
open Spine NativeIteratorStrictTargets NativeClosedApplication NativeIndexedCarrierTargets NativeIndexedCarrierSubtype
open NativeOrdinalBasisTargets NativeOrdinalBasisChecks NativeOrdinalCapPathsTargets
open NativeTowerWitnessPrefixTargets NativeTowerWitnessPrefixProof NativeTowerWitnessFamilyProof
open NativeTowerBetaPathProof NativeTowerIndexedEntryTargets NativeTowerIndexedEntryProof
open NativeTowerIndexedFiniteOrbitProof NativeTowerInnerMapSubstitutionProof NativeTowerInnerMapHigherIteratorProof
open NativeIndexedCarrierFiniteOrbitProof NativeIndexedCarrierOrbitBlocksProof

private theorem baseTrans {S} {a b c : ClosedNativeTerm S indexType}
    (ab : NativeBelow a b) (bc : NativeBelow b c) : NativeBelow a c :=
  StablePairProof.strictTransitive S c.val b.val a.val bc ab

private theorem runStrict {S} {n : Nat} {a b : ClosedNativeTerm S indexType}
    (run : StrictRun S n a b) : n ≠ 0 → NativeBelow b a := by
  induction run with
  | nil => intro ne; exact False.elim (ne rfl)
  | @cons k _ _ _ _ edge tail ih =>
    intro _
    cases k with
    | zero =>
      cases tail
      exact edge
    | succ k =>
      exact baseTrans (ih (Nat.succ_ne_zero k)) edge

theorem exact_OriginalPaidDrainStrict (S : Signature) (l : Nat) :
    ∀ (before after : ClosedNativeTerm S (ty l)), NativeBelow before after →
      NativeBelow (applyPaidDrain S l before) (applyPaidDrain S l after) := by
  induction l with
  | zero => intro before after edge; exact edge
  | succ l ih =>
    intro before after edge
    exact ih _ _ (NativeClosedApplicationChecks.exact_NativeApplicationFunctionStrict S
      (ty l) (ty l) after before (paidOperand S l) edge)

/-- The actual evaluated inner body at literal omega lies strictly below
the *fixed* original t_(l+2), not just an unrelated generated cap. -/
theorem exact_ActualTowerInnerOmegaEndpointBelow (S : Signature) (l : Nat) :
    NativeBelow (applyPaidDrain S l (printedIndexedHead S l (closedOmega S)))
      (closedTower S (l+2)) := by
  obtain ⟨mapping,seed,out,realMap,realSeed,realOut,run⟩ := exact_NativeTowerIndexedEntry S l
  let outer := indexedTerm .base mapping seed (closedOmega S)
  have outExact : out = outer := by
    apply Subtype.ext
    change out.val = indexedW .base mapping.val seed.val omegaCarrier
    rw [realMap,realSeed]
    exact realOut
  have outBelow : NativeBelow outer (closedTower S (l+2)) := by
    rw [← outExact]
    exact runStrict run (by omega)
  have omegaBelowT0 : NativeBelow (closedOmega S) (closedT0 S) :=
    exact_SameTypedNativeApplicationSelect (nativeNb S) (closedOmega S)
  have seedExact : seed = applyClosed (closedSuccessor S) (closedT0 S) := Subtype.ext realSeed
  have t0BelowSeed : NativeBelow (closedT0 S) seed := by
    rw [seedExact]
    exact exact_SameTypedNativeApplicationSelect (closedSuccessor S) (closedT0 S)
  have seedBelowOuter : NativeBelow seed outer :=
    exact_IndexedCarrierFiniteSeedOrbit .base mapping seed (closedOmega S) 0
  have low : NativeBelow (closedOmega S) outer :=
    baseTrans (baseTrans omegaBelowT0 t0BelowSeed) seedBelowOuter
  have appliedBelowOuter : NativeBelow (applyClosed mapping (closedOmega S)) outer :=
    exact_IndexedCarrierFiniteAbsorption .base mapping seed (closedOmega S) (closedOmega S) low 1
  have endpointBelow : NativeBelow (applyPaidDrain S l (printedIndexedHead S l (closedOmega S)))
      (applyClosed mapping (closedOmega S)) :=
    runStrict (exact_OriginalInnerMapHigherIteratorRun S l mapping (closedOmega S) realMap) (by decide)
  exact baseTrans (baseTrans endpointBelow appliedBelowOuter) outBelow

def originalInnerOrbitBlock (S : Signature) (l : Nat) (j : ClosedNativeTerm S indexType) (n : Nat) :
    ClosedNativeTerm S indexType :=
  applyPaidDrain S l (finiteApplication (actualArg S l) (printedIndexedHead S l j) n)

theorem exact_ActualTowerEarlierInnerOrbitBound (S : Signature) (l : Nat)
    (j : ClosedNativeTerm S indexType) (earlier : NativeBelow j (closedOmega S)) (n : Nat) :
    NativeBelow (originalInnerOrbitBlock S l j n) (closedTower S (l+2)) := by
  have edge : NativeBelow (finiteApplication (actualArg S l) (printedIndexedHead S l j) n)
      (printedIndexedHead S l (closedOmega S)) :=
    exact_IndexedCarrierFiniteEarlierOrbit (level l) (actualArg S l) (paidOperand S l)
      (closedOmega S) j earlier n
  exact baseTrans (exact_OriginalPaidDrainStrict S l _ _ edge) (exact_ActualTowerInnerOmegaEndpointBelow S l)

def fixedTowerOrbitImage (S : Signature) (l : Nat) (p : Nat × Nat) :
    ClosedNativeTerm S indexType :=
  originalInnerOrbitBlock S l (finiteIndex S p.1) p.2

def FixedTowerLex (p q : Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- Literal finite indices and inner-map argument copies simultaneously
realize strict natural-pair lex comparison inside the same actual tower bound. -/
theorem exact_ActualFixedTowerLexBlocks (S : Signature) (l : Nat) :
    (∀ p, NativeBelow (fixedTowerOrbitImage S l p) (closedTower S (l+2))) ∧
    (∀ p q, FixedTowerLex p q → NativeBelow (fixedTowerOrbitImage S l p) (fixedTowerOrbitImage S l q)) := by
  refine ⟨?_,?_⟩
  · intro p
    have omegaEq : cap (closedSuccessor S) (closedZero S) = closedOmega S := Subtype.ext rfl
    have earlier : NativeBelow (finiteIndex S p.1) (closedOmega S) := by
      rw [← omegaEq]
      exact (exact_CapAboveFiniteApplications S indexType (closedSuccessor S) (closedZero S) p.1).2
    exact exact_ActualTowerEarlierInnerOrbitBound S l (finiteIndex S p.1) earlier p.2
  · intro p q smaller
    rcases p with ⟨i,m⟩
    rcases q with ⟨j,n⟩
    rcases smaller with earlier | ⟨same,inside⟩
    · have idx : NativeBelow (finiteIndex S i) (finiteIndex S j) :=
        exact_SameTypedNativeFiniteOrbitStrict (closedSuccessor S) (closedZero S) earlier
      exact exact_OriginalPaidDrainStrict S l _ _
        (exact_IndexedOrbitBlockSeparation (level l) (actualArg S l) (paidOperand S l)
          (finiteIndex S i) (finiteIndex S j) idx m n)
    · change i = j at same
      subst j
      exact exact_OriginalPaidDrainStrict S l _ _
        (exact_SameTypedNativeFiniteOrbitStrict (actualArg S l)
          (printedIndexedHead S l (finiteIndex S i)) inside)

#print axioms exact_OriginalPaidDrainStrict
#print axioms exact_ActualTowerInnerOmegaEndpointBelow
#print axioms exact_ActualTowerEarlierInnerOrbitBound
#print axioms exact_ActualFixedTowerLexBlocks

end LogicLineages.PersistentMarking.NativeTowerBoundedInnerOrbitBlocksProof
